package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Requirements;
import hk.ust.cse.ObjectGen.Generation.Generators.ObjectGenerator;
import hk.ust.cse.ObjectGen.Generation.Generators.ParamReqDeductor;
import hk.ust.cse.ObjectGen.Generation.Generators.ParamReqDeductor.DeductResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.util.Utils;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class TreeSummarySelector extends AbstractSummarySelector {

  public TreeSummarySelector(List<Summary> summaries, Requirement req, IR ir, 
      boolean isFactoryOrCreateInner, ObjectGenerator objGenerator) {

    m_paramOrder    = new ArrayList<String>();
    m_paramTrees    = new Hashtable<String, Tree>();
    m_deductResults = new Hashtable<Summary, DeductResult>();
    
    // obtain the immediate fields in req
    List<List<String>> targetFields = objGenerator.getTargetFields(req);
    
    ParamReqDeductor deductor = new ParamReqDeductor(ir, isFactoryOrCreateInner, objGenerator);
    for (Summary summary : summaries) {
      // check if this summary can potentially modify the target fields in req
      boolean useful = isSummaryUseful(summary, req, targetFields, ir);
      if (!useful) {
        continue; // try next summary
      }
      
      // check if this summary contains bad size
      boolean badSize = isSummaryBadSize(summary, req, targetFields, ir);
      if (badSize) {
        continue;
      }
      
      // deduct parameters' requirements
      DeductResult deductResult = deductor.deductChildReqs(summary, req);
      if (deductResult == null) {
        continue; // try next summary
      }
      
      // build tree for each parameter's requirement
      Requirements childReqs = deductResult.childReqs;
      Enumeration<String> keys = childReqs.keys();
      while (keys.hasMoreElements()) {
        String topVarName = (String) keys.nextElement();
        Requirement childReq = childReqs.getRequirement(topVarName);
        
        Tree paramTree = m_paramTrees.get(topVarName);
        if (paramTree == null) {
          paramTree = new Tree();
          m_paramTrees.put(topVarName, paramTree);
          m_paramOrder.add(topVarName);
        }
        paramTree.addToTree(summary, childReq);
      }
      
      m_deductResults.put(summary, deductResult);
    }
    
    // sort by size
    Collections.sort(m_paramOrder, new Comparator<String>() {
      @Override
      public int compare(String o1, String o2) {
        return m_paramTrees.get(o2).getSize() - m_paramTrees.get(o1).getSize();
      }
    });
  }

  @Override
  public boolean hasNext() {
    return m_deductResults.size() > 0;
  }
  
  @Override
  // find the summary which has the same prefix of satisfied childReqs as the previous one
  public Summary nextSummary(List<Requirement> prevSatReqs) {
    List<String> prevSatParamNames = new ArrayList<String>();
    for (Requirement prevSatReq : prevSatReqs) {
      prevSatParamNames.add(prevSatReq.getVarName());
    }
    
    List<Summary> prevLevel = null;
    List<Summary> currLevel = null;
    for (String paramName : m_paramOrder) {
      int index = prevSatParamNames.indexOf(paramName);
      if (index >= 0) {
        prevLevel = currLevel;
        
        Tree tree     = m_paramTrees.get(paramName);
        TreeNode node = tree.findNodeWithReq(prevSatReqs.get(index));
        if (node != null) {
          List<Summary> nodeSummaries = node.getSummaries();
          currLevel = prevLevel == null ? nodeSummaries : 
                                          new ArrayList<Summary>(Utils.intersect(prevLevel, nodeSummaries));
          if (currLevel.size() == 0) { // no intersect summary, backtrack
            currLevel = prevLevel;
            break;
          }
        }
        else { // the node has been removed due to previous summary removal
          currLevel = prevLevel;
          break;
        }
      }
    }
    
    Summary next = null;
    if (currLevel != null && currLevel.size() > 0) {
      next = currLevel.get(0);
    }
    else {
      for (int i = 0, size = m_paramOrder.size(); i < size && next == null; i++) {
        Tree tree = m_paramTrees.get(m_paramOrder.get(i));
        if (tree.getSize() > 0) {
          next = tree.getRoot().getChildren().get(0).getSummaries().get(0);
        }
      }
    }
    return next;
  }

  @Override
  public void informChildReqSat(Requirement childReq, Sequence seq) {
  }

  @Override
  public void informChildReqNotSat(Requirement childReq) {
    Tree paramTree = m_paramTrees.get(childReq.getVarName());
    TreeNode node = paramTree.findNodeWithReq(childReq);
    if (node != null) {
      // find all summaries at and below this node
      List<Summary> notSatisfiables = paramTree.findSummariesInSubTree(node);
      
      // remove sub-tree
      paramTree.removeSubTree(node);
      
      // since all summaries cannot be satisfied due to this childReq (or 
      // requirement stronger than this childReq), remove them from everywhere
      Enumeration<String> keys = m_paramTrees.keys();
      while (keys.hasMoreElements()) {
        String key = (String) keys.nextElement();
        Tree tree = m_paramTrees.get(key);
        tree.removeSummaries(notSatisfiables);
      }
      for (Summary summary : notSatisfiables) {
        m_deductResults.remove(summary);
      }
    }
  }

  @Override
  public List<String> createEnsureGenOrder(List<String> paramNames) {
    List<String> ensureGenOrder = new ArrayList<String>();
    for (String paramName : m_paramOrder) {
      if (paramNames.contains(paramName)) {
        ensureGenOrder.add(paramName);
      }
    }
    return ensureGenOrder;
  }
  
  @Override
  public DeductResult getDeductResult(Summary summary) {
    return m_deductResults.get(summary);
  }

  @Override
  public int getSummaryCount() {
    return m_deductResults.size();
  }

  private final List<String>                     m_paramOrder;
  private final Hashtable<String, Tree>          m_paramTrees;
  private final Hashtable<Summary, DeductResult> m_deductResults;
  
  private static class Tree {
    public Tree() {
      m_root       = new TreeNode(null, new Requirement(""));
      m_reqNodeMap = new Hashtable<Requirement, TreeNode>();
    }
    
    public TreeNode addToTree(Summary summary, Requirement summaryChildReq) {
      TreeNode addedTo = addToTree(m_root, summary, summaryChildReq);
      m_reqNodeMap.put(summaryChildReq, addedTo);
      return addedTo;
    }
    
    private TreeNode addToTree(TreeNode node, Summary summary, Requirement summaryChildReq) {
      TreeNode addedTo = null;
      
      Requirement nodeReq = node.getRequirement();
      if (summaryChildReq.subsumes(nodeReq)) {
        if (nodeReq.compareStringSize() == summaryChildReq.compareStringSize()) {
          node.addSummary(summary);
          addedTo = node;
        }
        else {
          for (int i = 0, size = node.getChildren().size(); i < size && addedTo == null; i++) {
            TreeNode child = node.getChildren().get(i);
            addedTo = addToTree(child, summary, summaryChildReq);
          }
          
          if (addedTo == null) {
            addedTo = node.createChild(summary, summaryChildReq);
          }
        }
      }
      return addedTo;
    }
    
    public TreeNode findNodeWithReq(Requirement req) {
      return m_reqNodeMap.get(req);
    }
    
    public List<Summary> findSummariesInSubTree(TreeNode subTreeRoot) {
      List<Summary> summaries = new ArrayList<Summary>();
      
      summaries.addAll(subTreeRoot.getSummaries());
      for (TreeNode childNode : subTreeRoot.getChildren()) {
        summaries.addAll(findSummariesInSubTree(childNode));
      }
      
      return summaries;
    }
    
    public List<Requirement> findReqsInSubTree(TreeNode subTreeRoot) {
      List<Requirement> reqs = new ArrayList<Requirement>();
      
      reqs.add(subTreeRoot.getRequirement());
      for (TreeNode childNode : subTreeRoot.getChildren()) {
        reqs.addAll(findReqsInSubTree(childNode));
      }
      
      return reqs;
    }
    
    public boolean removeSubTree(TreeNode subTreeRoot) {
      TreeNode parent = subTreeRoot.getParent();
      if (parent != null) {
        parent.removeChild(subTreeRoot);
        
        // remove req - treeNode mappings m_reqNodeMap
        List<Requirement> reqs = findReqsInSubTree(subTreeRoot);
        for (Requirement req : reqs) {
          m_reqNodeMap.remove(req);
        }
        
        return true;
      }
      else {
        return false;
      }
    }
    
    public void removeSummaries(List<Summary> summaries) {
      removeSummaries(m_root, summaries);
    }
    
    private void removeSummaries(TreeNode node, List<Summary> summaries) {
      // remove summaries from bottom-up
      List<TreeNode> childNodes = new ArrayList<TreeNode>(node.getChildren());
      for (TreeNode childNode : childNodes) {
        removeSummaries(childNode, summaries);
      }
      node.removeSummaries(summaries);

      TreeNode parent = node.getParent();
      if (node.getSummaries().size() == 0 && parent != null) {
        for (TreeNode childNode : node.getChildren()) {
          parent.addChild(childNode);
        }
        parent.removeChild(node);
        
        m_reqNodeMap.remove(node.getRequirement());
      }
    }
    
    public TreeNode getRoot() {
      return m_root;
    }
    
    public int getSize() {
      return m_reqNodeMap.size();
    }
    
    private final TreeNode                         m_root;
    private final Hashtable<Requirement, TreeNode> m_reqNodeMap;
  }
  
  private static class TreeNode {
    
    public TreeNode(TreeNode parent, Requirement req) {
      m_parent      = parent;
      m_childNodes  = new ArrayList<TreeNode>();
      m_summaries   = new ArrayList<Summary>();
      m_requirement = req;
    }
    
    // add one more summary to this node
    public void addSummary(Summary summary) {
      m_summaries.add(summary);
    }
    
    public void removeSummaries(List<Summary> summaries) {
      m_summaries.removeAll(summaries);
    }
    
    public TreeNode createChild(Summary summary, Requirement req) {
      TreeNode child = new TreeNode(this, req);
      child.addSummary(summary);
      m_childNodes.add(child);
      return child;
    }
    
    public void addChild(TreeNode node) {
      m_childNodes.add(node);
      node.resetParent(this);
    }
    
    public void removeChild(TreeNode node) {
      m_childNodes.remove(node);
      node.resetParent(null);
    }
    
    public List<TreeNode> getChildren() {
      return m_childNodes;
    }
    
    public void resetParent(TreeNode parent) {
      m_parent = parent;
    }
    
    public TreeNode getParent() {
      return m_parent;
    }
    
    public List<Summary> getSummaries() {
      return m_summaries;
    }
    
    public Requirement getRequirement() {
      return m_requirement; 
    }

    private TreeNode             m_parent;
    private final List<TreeNode> m_childNodes;
    private final List<Summary>  m_summaries;
    private final Requirement    m_requirement;
  }
}
