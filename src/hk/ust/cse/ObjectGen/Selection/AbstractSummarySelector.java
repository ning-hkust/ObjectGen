package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Generators.ParamReqDeductor.DeductResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.Prevision.VirtualMachine.Reference;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import com.ibm.wala.ssa.IR;

public abstract class AbstractSummarySelector {
  public AbstractSummarySelector() {}
  
  public abstract boolean hasNext();
  
  public abstract Summary nextSummary(List<Requirement> prevSatReqs);
  
  public abstract void informChildReqSat(Requirement childReq, Sequence seq);
  
  public abstract void informChildReqNotSat(Requirement childReq);
  
  public abstract List<String> createEnsureGenOrder(List<String> paramNames);
  
  public abstract DeductResult getDeductResult(Summary summary);
  
  public abstract int getSummaryCount();

  // check if this summary can potentially modify the target fields
  protected boolean isSummaryUseful(Summary summary, Requirement req, List<List<String>> targetFields, IR ir) {
    boolean useful = targetFields.size() == 0;

    // collection parameters or static field class name
    List<String> params = new ArrayList<String>();
    if (req.getTargetInstance().getLastRefName().startsWith("L")) {
      String staticFieldClass = req.getTargetInstance().getLastRefName();
      params.add(staticFieldClass);
    }
    else {
      for (int i = 1, size = ir.getNumberOfParameters(); i <= size; i++) {
        params.add("v" + i);
      }
      params.add("RET");
    }

    for (int i = 0, size = params.size(); i < size && !useful; i++) {
      Reference paramRef = summary.getEffect().get(params.get(i));
      
      // could change only one field would be enough
      for (int j = 0, size2 = targetFields.size(); j < size2 && paramRef != null && !useful; j++) {
        List<String> targetFieldLink = targetFields.get(j);
        Reference fieldRef = paramRef;
        
        for (int k = 0, size3 = targetFieldLink.size(); k < size3 && fieldRef != null && !useful; k++) {
          fieldRef = fieldRef.getInstance().getField(targetFieldLink.get(k));
          if (fieldRef != null && fieldRef.getInstance().getLastReference() != fieldRef) { // not just reading the field
            useful = true;
          }
        }
      }
    }
    
    return useful;
  }
  
  // check if this summary has -100 size
  protected boolean isSummaryBadSize(Summary summary, Requirement req, List<List<String>> targetFields, IR ir) {
    boolean bad = false;
    
    // collection parameters or static field class name
    List<String> params = new ArrayList<String>();
    if (req.getTargetInstance().getLastRefName().startsWith("L")) {
      String staticFieldClass = req.getTargetInstance().getLastRefName();
      params.add(staticFieldClass);
    }
    else {
      for (int i = 1, size = ir.getNumberOfParameters(); i <= size; i++) {
        params.add("v" + i);
      }
      params.add("RET");
    }
    
    HashSet<Reference> checked = new HashSet<Reference>();
    for (int i = 0, size = params.size(); i < size && !bad; i++) {
      Reference paramRef = summary.getEffect().get(params.get(i));
      if (paramRef != null && !checked.contains(paramRef)) {
        bad = isSummaryBadSize(paramRef, checked);
      }
    }
    
    return bad;
  }
  
  private boolean isSummaryBadSize(Reference ref, HashSet<Reference> checked) {
    String fieldName  = ref.getName();
    String fieldValue = ref.getInstance().getValue();
    if (fieldValue != null && fieldValue.equals("#!-100") && (fieldName.equals("size") || fieldName.equals("count"))) {
      Reference parent = ref.getDeclaringInstance().getLastReference();
      if (parent != null) {
        String parentType = parent.getType().toLowerCase();
        if (parentType.contains("map") || parentType.contains("table")) {
          return true;
        }
      }
    }
    checked.add(ref);
    
    boolean bad = false;
    Iterator<Reference> iter = ref.getInstance().getFields().iterator();
    while (iter.hasNext() && !bad) {
      Reference field = (Reference) iter.next();
      if (field != null && !checked.contains(field)) {
        bad = isSummaryBadSize(field, checked);
      }
    }
    return bad;
  }
}
