package hk.ust.cse.ObjectGen.Summary;

import hk.ust.cse.ObjectGen.IntraSummary.IntraSummaryExtractor;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.PathCondition.Formula.SMT_RESULT;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.VirtualMachine.AbstractMemory;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision.VirtualMachine.Relation;
import hk.ust.cse.Prevision_PseudoImpl.PseudoImplMap;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.Wala.MethodMetaData;
import hk.ust.cse.Wala.SubClassHack;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import javax.naming.TimeLimitExceededException;

import com.ibm.wala.ssa.IR;

public class SummaryExtractor {

  public SummaryExtractor(String appJar, String pseudoImplJar) throws Exception {
    m_intraExtractor  = new IntraSummaryExtractor(appJar, pseudoImplJar);
    m_walaAnalyzer    = m_intraExtractor.getWalaAnalyzer();
    m_smtChecker      = m_intraExtractor.getExecutor().getSMTChecker();
    m_summaryDatabase = new SummaryDatabase("./summaries/", 20, m_walaAnalyzer);
    
    // load jar file, _removed.jar version is for faster call graph construction. Since it may 
    // be missing some classes (e.g. UnknownElement), we should use the full version in classloader
    appJar = appJar.endsWith("_removed.jar") ? appJar.substring(0, appJar.length() - 12) + ".jar" : appJar;
    Utils.loadJarFile(appJar);
  }

  // extract summaries, starting point
  public List<Summary> extract(String methodSig, boolean saveSummaries, long maxExtractTime, 
      HashSet<String> allMethodSet, HashSet<String> filterSet, HashSet<String> extractedSet) throws TimeLimitExceededException {
    return extract(methodSig, methodSig, saveSummaries, maxExtractTime, 0, 1, 
        new int[] {Integer.MAX_VALUE}, new ArrayList<String>(), allMethodSet, filterSet, extractedSet);
  }
  
  // maxExtractTime is only used to decide the maxExpandTime for each intra-summary, time for 
  // extracting sub-methods are not counted, thus the total time may extend way beyond this time
  private List<Summary> extract(String methodSig, String superMethodSig, boolean saveSummaries, 
      long maxExtractTime, int curRecDepth, int maxRecDepth, int[] recurExpand, List<String> expandings, 
      HashSet<String> allMethodSet, HashSet<String> filterSet, HashSet<String> extractedSet) throws TimeLimitExceededException {

    // initialize status to 'failed'
    s_lastStatus = -1;
    
    try {
      // obtain initial intra-summaries of the method
      //List<Summary> intraSummaries = m_intraExtractor.extract(methodSig, saveSummaries, 30000);
      List<Summary> intraSummaries = m_intraExtractor.getIntraSummaryDatabase().readSummaries(methodSig);
      if (intraSummaries != null && intraSummaries.size() > 0) {
        // average the time for each intra-summaries' expand
        long maxExpandTime = maxExtractTime / intraSummaries.size();
        maxExpandTime = maxExpandTime < 1000 ? 1000 : maxExpandTime; // at least one second
        
        // sort the intra-summaries by invocation numbers
        final Hashtable<Summary, Integer> invocationCountMap = new Hashtable<Summary, Integer>();
        for (Summary intraSummary : intraSummaries) {
          Collection<Reference> invocations = intraSummary.findAllInvocations();
          invocationCountMap.put(intraSummary, invocations.size());
        }
        Collections.sort(intraSummaries, new Comparator<Summary>() {
          @Override
          public int compare(Summary o1, Summary o2) {
            return invocationCountMap.get(o1) - invocationCountMap.get(o2);
          }
        });
        
        // expand all intra-summaries one by one
        expandings.add(superMethodSig);
        printStepSpaces(expandings.size());
        System.out.println("Expanding invocation: " + superMethodSig + " (actual target: " + methodSig + ")");
        
        int[] thisRecrFrom = new int[] {Integer.MAX_VALUE};
        List<Summary> expanded = new ArrayList<Summary>();
        for (int i = 0, oldSize = 0, size = intraSummaries.size(); i < size; i++, oldSize = expanded.size()) {
          expanded.addAll(expandInvocation(intraSummaries.get(i), saveSummaries, maxExpandTime, maxExtractTime, 
              curRecDepth, maxRecDepth, thisRecrFrom, expandings, allMethodSet, filterSet, extractedSet));

          printStepSpaces(expandings.size());
          System.out.print((i + 1) + " / " + size + " intra summaries expanded, current size: " + expanded.size());
          System.out.println(" (" + methodSig + ")");
          if (saveSummaries && curRecDepth == 0 && 
              (thisRecrFrom[0] == Integer.MAX_VALUE || expandings.size() - 1 <= thisRecrFrom[0])) {
            // save the newly got summaries to database
            m_summaryDatabase.saveSummariesAppend(methodSig, expanded, oldSize);
          }
          s_lastStatus = (expanded.size() > 0) ? 0 : -1; // partially finished
        }
        s_lastStatus = 1; // finished successfully
        
        if (saveSummaries && curRecDepth == 0 && 
            (thisRecrFrom[0] == Integer.MAX_VALUE || expandings.size() - 1 <= thisRecrFrom[0])) {
          extractedSet.add(methodSig);
        }
        expandings.remove(expandings.size() - 1);
        
        // record the outer most referred recursion method
        recurExpand[0] = thisRecrFrom[0] < recurExpand[0] ? thisRecrFrom[0] : recurExpand[0];
        return expanded;
      }
      else {
        System.err.println("Failed to load any intra-summaries for method: " + methodSig);
        return null;
      }
    } catch (Exception e) {
      e.printStackTrace();
      return null;
    }
  }

  // expand invocation effect for one intra-summary
  private List<Summary> expandInvocation(Summary intraSummary, boolean saveSummaries, long maxExpandTime, 
      long maxExtractTime, int curRecDepth, int maxRecDepth, int[] recurFrom, List<String> expandings, 
      HashSet<String> allMethodSet, HashSet<String> filterSet, HashSet<String> extractedSet) throws TimeLimitExceededException {

    List<Summary> lastExpanded = new ArrayList<Summary>();
    
    // find all invocations and sort them according to time
    Collection<Reference> invocations = intraSummary.findAllInvocations();
    List<Reference> sortedInvocations = new ArrayList<Reference>(invocations);
    Collections.sort(sortedInvocations, new Comparator<Reference>() {
      @Override
      public int compare(Reference arg0, Reference arg1) {
        Long time0 = Long.parseLong(arg0.getName().substring(arg0.getName().lastIndexOf("_") + 1));
        Long time1 = Long.parseLong(arg1.getName().substring(arg1.getName().lastIndexOf("_") + 1));
        return time1.compareTo(time0);
      }
    });
    
    // reached max recursive depth
    if (curRecDepth >= maxRecDepth) {
      String methodSig = intraSummary.getMethodData().getMethodSignature();
      System.err.println("Max recursion depth with (" + methodSig + "), discard summary.");
      return lastExpanded;
    }
    
    // expand all invocations one by one from the latest
    long totalSpent = 0;
    long timePerInvocation = maxExpandTime / (sortedInvocations.size() == 0 ? 1 : sortedInvocations.size());
    lastExpanded.add(intraSummary);
    for (int i = 0, size = sortedInvocations.size(); i < size && lastExpanded.size() > 0; i++) {
      Reference invocation = sortedInvocations.get(i);

      printStepSpaces(expandings.size());
      System.out.println("Merging: " + (i + 1) + " / " + size + " callee invocation: " + invocation.getName());
      
      // obtain the summaries (fully expanded) of this invocation
      List<List<Summary>> calleeSummariesList = new ArrayList<List<Summary>>();
      
      int index1 = invocation.getName().lastIndexOf('_');
      int index2 = invocation.getName().lastIndexOf('.');
      String methodSig = invocation.getName().substring(0, index1);
      String declClass = invocation.getName().substring(0, index2);

      // use pseudo implementations when necessary
      if (m_intraExtractor.getExecutor().usePseudo()) {
        String pseudoImpl = PseudoImplMap.findPseudoImpl(methodSig);
        methodSig = pseudoImpl != null ? pseudoImpl : methodSig;
      }
      
      boolean inAllMethodList = allMethodSet.contains(methodSig);
      if (!inAllMethodList) {
        IR ir = Jar2IR.getIR(m_walaAnalyzer, methodSig);
        if (ir != null) {
          // AbstractList$ListItr.checkForComodification()V -> AbstractList$Itr.
          // checkForComodification()V as ListItr's method is directly inherited from Itr
          methodSig = ir.getMethod().getSignature(); 
        }
      }
      
      // only extract sub-methods that are in the allMethodSet
      List<Summary> calleeSummaries = null;
      if (allMethodSet.contains(methodSig) && !filterSet.contains(methodSig)) {
        boolean isRecuresive = expandings.contains(methodSig);
        if (isRecuresive && curRecDepth + 1 >= maxRecDepth) {
          int thisRecurFrom = expandings.indexOf(methodSig);
          recurFrom[0] = thisRecurFrom < recurFrom[0] ? thisRecurFrom : recurFrom[0];
        }
        calleeSummaries = getSummaries(methodSig, methodSig, saveSummaries, 
            maxExtractTime, curRecDepth + (isRecuresive ? 1 : 0), maxRecDepth, 
            recurFrom, expandings, allMethodSet, filterSet, extractedSet);
      }
      
      // may be interface/abstract method
      if (calleeSummaries == null) {
        // try the invocation in sub-classes
        HashSet<IR> addedIR = new HashSet<IR>();
        List<String> subClasses = WalaUtils.getSubClasses(m_walaAnalyzer, declClass, true, false);
        subClasses = sortSubClasses(declClass, subClasses, subClasses.size());
        for (int j = 0, size2 = subClasses.size(); j < size2 && calleeSummariesList.size() < 2 /* max sub-classes use */; j++) {
          String subMethodSig = 
              Utils.getClassTypeJavaStr(subClasses.get(j), false) + invocation.getName().substring(index2, index1);

          // convert to the actual implementation: e.g. ArrayList.iterate() -> AbstractList.iterator()
          IR ir = Jar2IR.getIR(m_walaAnalyzer, subMethodSig);
          subMethodSig = ir.getMethod().getSignature(); 
          
          // only extract sub-methods that are in the allMethodSet
          if (allMethodSet.contains(subMethodSig) && !filterSet.contains(subMethodSig)) {
            if (!addedIR.contains(ir)) {
              boolean isRecuresive = expandings.contains(methodSig); /* use the super class */
              if (isRecuresive && curRecDepth + 1 >= maxRecDepth) {
                int thisRecurFrom = expandings.indexOf(methodSig);
                recurFrom[0] = thisRecurFrom < recurFrom[0] ? thisRecurFrom : recurFrom[0];
              }
              calleeSummaries = getSummaries(subMethodSig, methodSig, saveSummaries, 
                  maxExtractTime, curRecDepth + (isRecuresive ? 1 : 0), maxRecDepth, 
                  recurFrom, expandings, allMethodSet, filterSet, extractedSet);
              if (calleeSummaries != null) {
                calleeSummariesList.add(calleeSummaries);
                addedIR.add(ir);
              }
            }
          }
        }
      }
      else if (calleeSummaries != null) {
        calleeSummariesList.add(calleeSummaries);
      }
      
      // when failed to obtain any summary for invocation, create an empty 
      // summary to trigger the merge of hidden effect, which essentially 
      // means we discard the potential effect of the invocation to the 
      // parameters. But this cannot fix the RET used by the current summary
      if (calleeSummariesList.size() == 0) {
        System.err.println("Failed to obtain summaries for invocation (including sub-classes): " + 
            methodSig + ". Discard side-effects.");

        List<Summary> fakeSummaries = new ArrayList<Summary>();
        IR ir = Jar2IR.getIR(m_walaAnalyzer, methodSig);
        MethodMetaData methData = ir != null ? new MethodMetaData(ir) : null;
        fakeSummaries.add(new Summary(new ArrayList<Condition>(), 
            new Hashtable<String, Reference>(), new Hashtable<String, Relation>(), methData));

        calleeSummariesList.add(fakeSummaries);
      }
      
      if (calleeSummariesList.size() > 0) {
        boolean partialOvertime = false;
        long lastStartExpandTime = System.currentTimeMillis();
        long maxTimeForInvocation = timePerInvocation * (i + 1);
        List<Summary> expandedInvocation = new ArrayList<Summary>();
        for (int j = 0, size2 = calleeSummariesList.size(); j < size2 && !partialOvertime; j++) {
          List<Summary> calleeSummaries2 = calleeSummariesList.get(j);

          // print status
          printStepSpaces(expandings.size());
          System.out.print(lastExpanded.size() + " caller summaries <- " + calleeSummaries2.size() + " callee summaries.");
          System.out.println((calleeSummaries2.size() > 0 && calleeSummaries2.get(0).getMethodData() != null) ? 
              " (" + calleeSummaries2.get(0).getMethodData().getMethodSignature() + ")" : "");
          
          // start merging callee summaries to caller
          for (int k = 0, size3 = lastExpanded.size(); k < size3 && !partialOvertime; k++) {
            Summary summary = lastExpanded.get(k);
            
            // this section takes the most time
            totalSpent += (System.currentTimeMillis() - lastStartExpandTime);
            if (totalSpent > maxTimeForInvocation) {
              partialOvertime = true;
              //System.out.println("Partial Overtime: " + maxTimeForInvocation + ", i == " + i);
              break;
            }
            
            lastStartExpandTime = System.currentTimeMillis();
            
            List<Summary> expandedInvs = expandInvocation(summary, invocation, calleeSummaries2);
            for (Summary expandedInv : expandedInvs) {
              // translate summary to a formula for smt check
              Formula formula = createValidatingFormula(expandedInv);
              //SMT_RESULT result = s_executor.getSMTChecker().smtCheck(formula, true, true, false);
              try {
                // for performance reason, we only do simple check
                SMT_RESULT result = m_smtChecker.simpleCheck(formula);
                if (result.equals(SMT_RESULT.SAT)) { // only add the satisfiable ones
                  expandedInvocation.add(expandedInv);
                }
              } catch (Throwable e) {
                // XXX bug
              }
            }
            System.out.print((k + 1) + ((((k + 1) % 20) == 0 || k == size3 - 1) ? "\n" : " "));
          }
        }
        lastExpanded = expandedInvocation; // ready to expand next invocation
      }
      
      if (totalSpent >= maxExpandTime) {
        if (i < sortedInvocations.size() - 1) {
          lastExpanded.clear(); // they are not fully expanded
        }
      }
    }
    
    // since we are using simple check instead of full SMT check during merging, it is possible 
    // that there might be unsatisfiable ones in the final list, do one more round of full SMT check
    for (int i = 0; i < lastExpanded.size(); i++) {
      Formula formula = createValidatingFormula(lastExpanded.get(i));
      try {
        SMT_RESULT result = m_smtChecker.smtCheck(formula, true, false, false, true, false, false);
        if (!result.equals(SMT_RESULT.SAT)) {
          lastExpanded.remove(i--);
        }
      } catch (Throwable e) {
        // XXX bug
        lastExpanded.remove(i--);
      }
    }
    
    return lastExpanded;
  }
  
  private Formula createValidatingFormula(Summary summary) {
    // add references to refMap
    Hashtable<String, Reference> effect = summary.getEffect();
    Hashtable<String, Hashtable<String, Reference>> refMap = new Hashtable<String, Hashtable<String, Reference>>();
    Hashtable<String, Reference> refMap2 = new Hashtable<String, Reference>();
    for (int i = 1; i <= summary.getMethodData().getParamList().size(); i++) {
      Reference reference = effect.get("v" + i);
      refMap2.put("v" + i, reference);
    }
    refMap.put("", refMap2);
    
    // relation map
    Hashtable<String, Relation> relationMap = summary.getRelationMap();
    
    // translate to Formula
    List<Condition> conditionList = summary.getPathConditions();
    Formula formula = new Formula(conditionList, new AbstractMemory(refMap, null, relationMap));
    return formula;
  }

  // expand the invocation effect of a particular invocation for one intra-summary
  private List<Summary> expandInvocation(Summary intraSummary, Reference invocation, List<Summary> calleeSummaries) {
    List<Summary> expanded = new ArrayList<Summary>();
    
    // if the intra-summary has been fully expanded with respect to this invocation
    if (intraSummary.fullyExpanded(invocation)) {
      expanded.add(intraSummary);
    }
    else {
      for (Summary calleeSummary : calleeSummaries) {
        try {          
          expanded.add(mergeSummaries(intraSummary, calleeSummary, invocation));
        } catch (Throwable e) {e.printStackTrace();}
      }
    }
    return expanded;
  }
  
  // create a new merged summary of the two summaries, will not affect summary1 and summary2
  private Summary mergeSummaries(Summary summary1, Summary summary2, Reference invocation) {  
    
    Hashtable<String, String> paramArgMap    = buildParamArgMap(invocation);
    Hashtable<Instance, Instance> replaceMap = new Hashtable<Instance, Instance>();
    
    // make clone to avoid affecting summary1 and summary2
    Summary cloneSummary1 = summary1.deepClone();
    Summary cloneSummary2 = summary2.deepClone();

    // pass the conversion helper instances to cloneSummary1 and paramArgMap
    passConversionHelpers(paramArgMap, cloneSummary1, cloneSummary2);
    
    // add instanceof statement if the actual summary's method is different from the invocation 
    // as it is the sub-class's method. exception for pseudo implementations
    if (summary2.getMethodData() != null && 
        !invocation.getName().startsWith(summary2.getMethodData().getMethodSignature()) && 
        !PseudoImplMap.isPseudoImpl(summary2.getMethodData().getMethodSignature())) {
      // summary2 is an summary for the method of a sub-class
      
      Instance topInstance = invocation.getInstance().getToppestInstance();
      if (topInstance.getLastReference() != null) { // avoid cases like: ##str.substring(...)
        String refName = topInstance.getLastRefName();
        Reference refRef = cloneSummary1.getEffect().get(refName);
        if (refRef != null) {
          TypeConditionTerm typeTerm = new TypeConditionTerm(refRef.getInstance(), 
              TypeConditionTerm.Comparator.OP_INSTANCEOF, summary2.getMethodData().getDeclaringClass(true));
          cloneSummary1.getPathConditions().add(new Condition(typeTerm));
        }
      }
    }

    HashSet<List<Instance>> mergedInstances = new HashSet<List<Instance>>();
    Hashtable<Instance, Instance> translatedMap = new Hashtable<Instance, Instance>();    
    Enumeration<String> keys = cloneSummary1.getEffect().keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Reference reference = cloneSummary1.getEffect().get(key);
      translatedMap.put(reference.getInstance(), reference.getInstance());
      for (Instance oldInstance : reference.getOldInstances()) {
        translatedMap.put(oldInstance, oldInstance);
      }
    }

    // handle potentially affected fields
    Collection<Instance> instances = cloneSummary1.findInvocationAsEffect(invocation);
    Iterator<Instance> iter = instances.iterator();
    Instance instance = iter.hasNext() ? iter.next() : null;
    while (instance != null) {
      cloneSummary1.mergeFieldEffect(
          instance, invocation, cloneSummary2, paramArgMap, translatedMap, mergedInstances, replaceMap);
      // after merge, this "_undecidable_" field is no longer useful for instance
      instance.getFieldSet().remove("_undecidable_" + invocation.getName());
      
      // next one
      instance = iter.hasNext() ? iter.next() : null;
      if (instance == null || (instance != null && replaceMap.containsKey(instance))) {
        // re-find invocation effected instances as instance2 has already been replaced
        instances = cloneSummary1.findInvocationAsEffect(invocation);
        iter = instances.iterator();
        instance = iter.hasNext() ? iter.next() : null;
      }
    }
    cloneSummary1 = replaceInstances(cloneSummary1, replaceMap);
    
    // merge the static field effect
    long invokeTime = Long.parseLong(invocation.getName().substring(invocation.getName().lastIndexOf('_') + 1));
    cloneSummary1.mergeStaticFieldEffect(cloneSummary2, 
        invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);

    // handle invocation return
    if (cloneSummary2.getEffect().containsKey("RET")) { // this invocation does not return void      
      instances = cloneSummary1.findInvocationAsReturn(invocation);
      iter = instances.iterator();
      instance = iter.hasNext() ? iter.next() : null;
      while (instance != null) {
        try {
          // cannot make sure retInstance (and its fields) are assigned later or earlier then instance (and its fields) and 
          // vice-versa, for example, org.apache.commons.collections.map.AbstractLinkedMap.init()V and 
          // org.apache.commons.collections.list.TreeList$AVLNode.rotateLeft (should have 60 results) are two opposite examples
          
          Reference retRef = cloneSummary2.getEffect().get("RET");
          Instance retInstance = retRef.getInstance();
          Instance replacedAs = replaceMap.get(retInstance);
          if (replacedAs != null) {
            cloneSummary1.mergeFieldEffect2(replacedAs, instance, invokeTime, null, translatedMap, mergedInstances, replaceMap);
            replaceMap.put(instance, replacedAs); // fieldInstance could exist in path condition list
          }
          else {
            retInstance = cloneSummary1.translateScope(
                retRef.getInstance(), paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);

            cloneSummary1.mergeFieldEffect2(instance, retInstance, invokeTime, null, translatedMap, mergedInstances, replaceMap);
            replaceMap.put(retInstance, instance); // fieldInstance could exist in path condition list

            // after merging field effects, mergeTo contains  all field effects of fieldInstance, 
            // now need to set mergeTo to what it is (constant) or where from (v6)
            cloneSummary1.setInstanceOrigin(instance, retInstance, retRef, retRef.getInstance(), replaceMap, invokeTime);

            // remove v1_v2 fields
            List<Reference> fieldRefs = new ArrayList<Reference>(instance.getFields());
            for (Reference fieldRef : fieldRefs) {
              if (fieldRef.getName().matches("v[0-9]+_(?:null|[v#][\\S]+)")) {
                instance.getFieldSet().remove(fieldRef.getName());
              }
            }
          }
        } catch (Throwable e) {
          // in case any unexpected exception happens, we can still continue;
        }
        // next one
        instance = iter.hasNext() ? iter.next() : null;
      }
    }

    // since this invocation is merged, remove caller's invocation field
    if (cloneSummary2.getEffect().containsKey("RET") || (cloneSummary2.getMethodData() != null && 
        cloneSummary2.getMethodData().getIR().getMethod().getReturnType().getName().toString().equals("V"))) {
      removeInvocationName(cloneSummary1, invocation.getName());
    }
    cloneSummary1 = replaceInstances(cloneSummary1, replaceMap);
    
    // merge path conditions (need to translate scope)
    List<Condition> pathConditions1 = cloneSummary1.getPathConditions();
    List<Condition> pathConditions2 = cloneSummary2.getPathConditions();
    pathConditions2 = translateScope(cloneSummary1, pathConditions2, 
        paramArgMap, translatedMap, mergedInstances, replaceMap);
    List<Condition> mergedConditions = new ArrayList<Condition>();
    mergedConditions.addAll(pathConditions1);
    mergedConditions.addAll(pathConditions2);
    
    // merge relationMap (need to translate scope)
    Hashtable<String, Relation> relationMap1 = cloneSummary1.getRelationMap();
    Hashtable<String, Relation> relationMap2 = cloneSummary2.getRelationMap();
    relationMap2 = translateScope(cloneSummary1, relationMap2, cloneSummary2, 
        paramArgMap, translatedMap, mergedInstances, replaceMap, invocation);
    Hashtable<String, Relation> mergedRelationMap = mergeRelationMap(relationMap1, relationMap2, invocation);
    
    Summary mergedSummary = new Summary(mergedConditions, 
        cloneSummary1.getEffect(), mergedRelationMap, cloneSummary1.getMethodData());

    // replace summaries in both path conditions and effect
    mergedSummary = replaceInstances(mergedSummary, replaceMap);
    return mergedSummary;
  }
  
  // relationMap2 must have been translated already
  private Hashtable<String, Relation> mergeRelationMap(Hashtable<String, Relation> relationMap1, 
                                                              Hashtable<String, Relation> relationMap2, Reference invocation) {
    Hashtable<String, Relation> mergedRelationMap = new Hashtable<String, Relation>(relationMap1);
    
    long invocationTime = Long.parseLong(invocation.getName().substring(invocation.getName().lastIndexOf('_') + 1));
    
    Enumeration<String> keys = relationMap2.keys();
    while (keys.hasMoreElements()) {
      String relName = (String) keys.nextElement();
      Relation relation2 = relationMap2.get(relName);
      
      if (!mergedRelationMap.containsKey(relName)) {
        mergedRelationMap.put(relName, relation2);
      }
      else {
        Relation relation1 = mergedRelationMap.get(relName);
        List<Instance[]> domainValues = relation1.getDomainValues();
        List<Instance>    rangeValues = relation1.getRangeValues();
        List<Long>      functionTimes = relation1.getFunctionTimes();
        
        // find the appropriate time to insert
        int insertIndex = functionTimes.size();
        for (int i = 0, size = functionTimes.size(); i < size; i++) {
          if (functionTimes.get(i) > invocationTime) {
            insertIndex = i;
            break;
          }
        }
        
        // insert functions
        for (int i = 0, size = relation2.getFunctionCount(); i < size; i++, insertIndex++) {
          domainValues.add(insertIndex, relation2.getDomainValues().get(i));
          rangeValues.add(insertIndex, relation2.getRangeValues().get(i));
          functionTimes.add(insertIndex, relation2.getFunctionTimes().get(i));
        }
      }
    }
    
    return mergedRelationMap;
  }
  
  // may affect the original instances, better use a clone version
  // translate to the scope of the current summary
  private List<Condition> translateScope(Summary toInv, List<Condition> pathConditions, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    List<Condition> translatedConds = new ArrayList<Condition>();

    for (Condition condition : pathConditions) {
      boolean oneTermTranslated = false;
      List<ConditionTerm> translatedTerms = new ArrayList<ConditionTerm>();
      for (ConditionTerm term : condition.getConditionTerms()) {
        boolean oneInstanceTranslated = false;
        List<Instance> translatedInstances = new ArrayList<Instance>();
        for (Instance instance : term.getInstances()) {
          Instance translated = toInv.translateScope(
              instance, paramArgMap, translatedMap, mergedInstances, replaceMap, null);
          translatedInstances.add(translated);
          oneInstanceTranslated |= translated != instance;
        }

        if (oneInstanceTranslated) {
          ConditionTerm translatedTerm = null;
          if (term instanceof BinaryConditionTerm) {
            translatedTerm = new BinaryConditionTerm(translatedInstances.get(0), 
                ((BinaryConditionTerm) term).getComparator(), translatedInstances.get(1));
          }
          else {
            translatedTerm = new TypeConditionTerm(translatedInstances.get(0), 
                ((TypeConditionTerm) term).getComparator(), ((TypeConditionTerm) term).getTypeString());
          }
          translatedTerms.add(translatedTerm);
          oneTermTranslated = true;
        }
        else {
          translatedTerms.add(term);
        }
      }
      translatedConds.add(oneTermTranslated ? new Condition(translatedTerms): condition);
    }
    return translatedConds;
  }
  
  // may affect the original instances, better use a clone version
  // translate to the scope of the current summary
  private Hashtable<String, Relation> translateScope(Summary toInv, Hashtable<String, Relation> relationMap, 
      Summary fromInv, Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap, Reference invocation) {

    Hashtable<String, Relation> translatedRelMap = new Hashtable<String, Relation>();
    
    long invocationTime = Long.parseLong(invocation.getName().substring(invocation.getName().lastIndexOf('_') + 1));
    
    Enumeration<String> keys = relationMap.keys();
    while (keys.hasMoreElements()) {
      String relName = (String) keys.nextElement();
      Relation relation = relationMap.get(relName);
      Relation translatedRel = new Relation(relation.getName(), 
          relation.getDomainDimension(), relation.getDirection());
      List<Instance[]> domainValuesList = translatedRel.getDomainValues();
      List<Instance>   rangeValueList   = translatedRel.getRangeValues();
      List<Long>      functionTimeList  = translatedRel.getFunctionTimes();
      
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        Instance[] tranDomainValues = new Instance[domainValues.length];
        for (int j = 0; j < domainValues.length; j++) {
          tranDomainValues[j] = toInv.translateScope(domainValues[j], 
              paramArgMap, translatedMap, mergedInstances, replaceMap, null);
        }
        domainValuesList.add(tranDomainValues);
        
        Instance transRangeValue = null;
        if (relation.getRangeValues().get(i) != null) {
          transRangeValue = toInv.translateScope(relation.getRangeValues().get(i), 
              paramArgMap, translatedMap, mergedInstances, replaceMap, null);
        }
        rangeValueList.add(transRangeValue);
        
        long newTime = invocationTime + i + 1;
        functionTimeList.add(newTime);
        
        // replace relation read instances
        if (relation.getRangeValues().get(i) == null) {
          String readStr = "read_" + relName + "_" + relation.getFunctionTimes().get(i);
          Set<Reference> references = fromInv.findRelationRead(readStr);
          for (Reference reference : references) {
            Reference replaced = new Reference("read_" + relName + "_" + newTime, reference.getType(), 
                "", new Instance("", reference.getInstance().getCreateBlock()), null, true);
            replaceMap.put(reference.getInstance(), replaced.getInstance());
            
            // merge fields into the new relation read instance
            toInv.mergeFieldEffect2(replaced.getInstance(), reference.getInstance(), 
                null, paramArgMap, translatedMap, mergedInstances, replaceMap);
            toInv.getEffect().put(replaced.getName(), replaced); // necessary for deepClone
          }
        }
      }
      
      translatedRelMap.put(relName, translatedRel);
    }
    
    return translatedRelMap;
  }
  
  // get fully expanded summaries for the method of this invocation
  private List<Summary> getSummaries(String methodSig, String superMethodSig, boolean saveSummaries, 
      long maxExtractTime, int curRecDepth, int maxRecDepth, int[] recurExpand, List<String> expandings, 
      HashSet<String> allMethodSet, HashSet<String> filterSet, HashSet<String> extractedSet) throws TimeLimitExceededException {
    
    // try to read from database
    List<Summary> summaries = null;
    if (!expandings.contains(methodSig) && extractedSet.contains(methodSig)) {
      summaries = m_summaryDatabase.readSummaries(methodSig);
    }
    if (summaries == null) {
      summaries = extract(methodSig, superMethodSig, saveSummaries, maxExtractTime, curRecDepth, maxRecDepth, 
          recurExpand, expandings, allMethodSet, filterSet, extractedSet);
    }
    
    return summaries;
  }
  
  private Hashtable<String, String> buildParamArgMap(Reference invocation) {
    Hashtable<String, String> paramArgMap = new Hashtable<String, String>();
    
    // argument-parameter information is stored in the fields of the invocation reference
    for (Reference field : invocation.getInstance().getFields()) {
      String fieldName = field.getName();
      int index = fieldName.indexOf("_");
      if (index >= 0) { // otherwise, could simply be a field read of the return value
        paramArgMap.put(fieldName.substring(0, index), fieldName.substring(index + 1));
      }
    }
    return paramArgMap;
  }
  
  // in rare cases, calleeInv may contain number conversion helper instances e.g., v27$1, in such 
  // cases, we pass these helper variables directly to the caller summary and paramArgMap
  private void passConversionHelpers(Hashtable<String, String> paramArgMap, Summary callerInv, Summary calleeInv) {
    Hashtable<String, Reference> effect = calleeInv.getEffect();
    Enumeration<String> keys = effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      if (key.matches("v[0-9]+\\$[0-9]+")) { // e.g. v27$1
        Reference refCallee = effect.get(key);
        Instance instance = refCallee.getInstance();
        
        // create a new name in caller: v27 + size + $1: v2712$1
        int index = key.lastIndexOf('$');
        String newName = key.substring(0, index) + callerInv.getEffect().size() + key.substring(index);
        
        // put to caller's effect and paramArgMap
        Reference refCaller = new Reference(newName, refCallee.getType(), refCallee.getCallSites(), 
            new Instance(instance.getInitCallSites(), instance.getCreateBlock()), refCallee.getDeclaringInstance(), true);
        callerInv.getEffect().put(newName, refCaller);
        paramArgMap.put(key, newName);
      }
    }
  }
  
  private Summary replaceInstances(Summary summary, Hashtable<Instance, Instance> replaceMap) {
    Hashtable<Instance, Instance> replacedMap = new Hashtable<Instance, Instance>();
    
    Hashtable<String, Reference> replacedEffect = summary.getEffect();
    List<Condition> replacedPathCond            = summary.getPathConditions();
    Hashtable<String, Relation> replacedRelMap  = summary.getRelationMap();
    
    int oldSize = -1;
    int totalLooped = 0;
    while (replaceMap.size() != oldSize && totalLooped++ < 10 /* avoid endless loop due to bugs */) {
      oldSize = replaceMap.size();
      
//      Enumeration<Instance> keys = replaceMap.keys();
//      while (keys.hasMoreElements()) {
//        Instance key = (Instance) keys.nextElement();
//        replaceInstance(key, replaceMap, replacedMap);
//      }
  
      replacedEffect   = replaceInstances(replacedEffect, replaceMap, replacedMap);
      replacedPathCond = replaceInstances(replacedPathCond, replaceMap, replacedMap);
      replacedRelMap   = replaceInstances1(replacedRelMap, replaceMap, replacedMap);
    }
    
    return new Summary(replacedPathCond, replacedEffect, replacedRelMap, summary.getMethodData());
  }
  
  private Hashtable<String, Reference> replaceInstances(Hashtable<String, Reference> methodRefs, 
      Hashtable<Instance, Instance> replaceMap, Hashtable<Instance, Instance> replacedMap) {
    Hashtable<String, Reference> replaced = new Hashtable<String, Reference>();
    
    Enumeration<String> keys = methodRefs.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Instance replacedInstance = replaceInstance(methodRefs.get(key).getInstance(), replaceMap, replacedMap);
      
      Reference reference = methodRefs.get(key);
      boolean setLastRef = replacedInstance == reference.getInstance() && 
                           reference.getInstance().getLastReference() == reference;
      Reference replacedRef = new Reference(reference.getName(), reference.getType(), reference.getCallSites(), 
          replacedInstance, reference.getDeclaringInstance(), setLastRef);

      replaced.put(key, replacedRef);
    }
    return replaced;
  }
  
  private  List<Condition> replaceInstances(List<Condition> pathConditions, 
      Hashtable<Instance, Instance> replaceMap, Hashtable<Instance, Instance> replacedMap) {
    
    List<Condition> replacedConds = new ArrayList<Condition>();
    for (Condition condition : pathConditions) {
      boolean oneTermReplaced = false;
      List<ConditionTerm> replacedTerms = new ArrayList<ConditionTerm>();
      for (ConditionTerm term : condition.getConditionTerms()) {
        boolean oneInstanceReplaced = false;
        List<Instance> replacedInstances = new ArrayList<Instance>();
        for (Instance instance : term.getInstances()) {
          Instance replaced = replaceInstance(instance, replaceMap, replacedMap);
          replacedInstances.add(replaced);
          oneInstanceReplaced |= replaced != instance;
        }

        if (oneInstanceReplaced) {
          ConditionTerm replacedTerm = null;
          if (term instanceof BinaryConditionTerm) {
            replacedTerm = new BinaryConditionTerm(replacedInstances.get(0), 
                ((BinaryConditionTerm) term).getComparator(), replacedInstances.get(1));
          }
          else {
            replacedTerm = new TypeConditionTerm(replacedInstances.get(0), 
                ((TypeConditionTerm) term).getComparator(), ((TypeConditionTerm) term).getTypeString());
          }
          replacedTerms.add(replacedTerm);
          oneTermReplaced = true;
        }
        else {
          replacedTerms.add(term);
        }
      }
      replacedConds.add(oneTermReplaced ? new Condition(replacedTerms) : condition);
    }
    return replacedConds;
  }
  
  private Hashtable<String, Relation> replaceInstances1(Hashtable<String, Relation> relationMap, 
      Hashtable<Instance, Instance> replaceMap, Hashtable<Instance, Instance> replacedMap) {

    Hashtable<String, Relation> replacedRelMap = new Hashtable<String, Relation>();
    
    Enumeration<String> keys = relationMap.keys();
    while (keys.hasMoreElements()) {
      String relName = (String) keys.nextElement();
      Relation relation = relationMap.get(relName);
      Relation replacedRel = new Relation(relation.getName(), 
          relation.getDomainDimension(), relation.getDirection());
      List<Instance[]> domainValuesList = replacedRel.getDomainValues();
      List<Instance>   rangeValueList   = replacedRel.getRangeValues();
      List<Long>      functionTimeList  = replacedRel.getFunctionTimes();
      
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        Instance[] replacedDomainValues = new Instance[domainValues.length];
        for (int j = 0; j < domainValues.length; j++) {
          replacedDomainValues[j] = replaceInstance(domainValues[j], replaceMap, replacedMap);
        }
        domainValuesList.add(replacedDomainValues);
        
        Instance replacedRangeValue = null;
        if (relation.getRangeValues().get(i) != null) {
          replacedRangeValue = replaceInstance(relation.getRangeValues().get(i), replaceMap, replacedMap);
        }
        rangeValueList.add(replacedRangeValue);
        
        functionTimeList.add(relation.getFunctionTimes().get(i));
      }
      
      replacedRelMap.put(relName, replacedRel);
    }
    
    return replacedRelMap;
  }

  private Instance replaceInstance(Instance instance, Hashtable<Instance, Instance> replaceMap, 
      Hashtable<Instance, Instance> replacedMap) {
    return replaceInstance(instance, replaceMap, replacedMap, new HashSet<Instance>());
  }

  private Instance replaceInstance(Instance instance, Hashtable<Instance, Instance> replaceMap, 
      Hashtable<Instance, Instance> replacedMap, HashSet<Instance> prevInstances) {

    if (prevInstances.contains(instance) || prevInstances.size() > 10 /* too much, likely due to a bug */) {
      return instance;
    }
    else {
      prevInstances.add(instance);
    }
    
    Instance replaced = null;
    if (replacedMap.containsKey(instance)) {
      replaced = replacedMap.get(instance);
    }
    else {
      replaced = instance;
      if (replaceMap.containsKey(instance)) {
        replaced = replaceMap.get(instance);
        replaced = replaceInstance(replaced, replaceMap, replacedMap, prevInstances);
        replacedMap.put(instance, replaced);
      }
      else {
        if (instance.isBounded() && !instance.isAtomic()) {
          Instance left  = replaceInstance(instance.getLeft(), replaceMap, replacedMap, prevInstances);
          Instance right = replaceInstance(instance.getRight(), replaceMap, replacedMap, prevInstances);
          if (left != instance.getLeft() || right != instance.getRight()) {
            replaced = new Instance(left, instance.getOp(), right, instance.getCreateBlock());
            replacedMap.put(instance, replaced);
            replacedMap.put(instance.getLeft(), left);
            replacedMap.put(instance.getRight(), right);
          }
        }
      }
      
      // even if instance == replaced, we still want to replace its fields
      replaceInstanceFields(replaced, replaceMap, replacedMap, prevInstances);
    }
    
    prevInstances.remove(instance);
    return replaced;
  }
  
  private void replaceInstanceFields(Instance instance, Hashtable<Instance, Instance> replaceMap, 
      Hashtable<Instance, Instance> replacedMap, HashSet<Instance> prevInstances) {
    
    for (Reference fieldRef : instance.getFields()) {
      Instance replaced = replaceInstance(fieldRef.getInstance(), replaceMap, replacedMap, prevInstances); 
      if (fieldRef.getInstance() != replaced) {
        boolean setLastRef = false;//fieldRef.getInstance().getLastReference() == fieldRef;
        instance.setField(fieldRef.getName(), fieldRef.getType(), fieldRef.getCallSites(), replaced, setLastRef, true);
        replaceMap.put(fieldRef.getInstance(), replaced);

        // set the life time for translated in fieldRefTo
        Reference fieldRefTo = instance.getField(fieldRef.getName());
        setInstanceLifeTime(fieldRefTo, fieldRef, replaced, fieldRef.getInstance(), null);
      }
      
      // also replace the instances in the oldInstance list
      Reference fieldRefTo = instance.getField(fieldRef.getName());
      for (Instance oldInstance : new ArrayList<Instance>(fieldRef.getOldInstances())) {
        Instance replacedOld = replaceInstance(oldInstance, replaceMap, replacedMap, prevInstances);
        if (replacedOld != oldInstance) {
          fieldRefTo.getOldInstances().remove(oldInstance);
          fieldRefTo.getOldInstances().add(replacedOld);
          setInstanceLifeTime(fieldRefTo, fieldRef, replacedOld, oldInstance, null);
          if (oldInstance.getLastReference() == fieldRef) {
            replacedOld.setLastReference(fieldRefTo);
          }
          replaceMap.put(oldInstance, replacedOld);
        }
      }
    }
  }
  
  private void removeInvocationName(Summary summary, String invocationName) {
    HashSet<Instance> removed = new HashSet<Instance>();
    
    Enumeration<String> keys = summary.getEffect().keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Reference reference = summary.getEffect().get(key);
      removeInvocationName(reference, invocationName, removed);
    }
    
    for (Condition condition : summary.getPathConditions()) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          removeInvocationName(instance, invocationName, removed);
        }
      }
    }
  }

  private void removeInvocationName(Reference reference, String invocationName, HashSet<Instance> removed) {
    removeInvocationName(reference.getInstance(), invocationName, removed);
    for (Instance oldInstance : reference.getOldInstances()) {
      removeInvocationName(oldInstance, invocationName, removed);
    }
  }
  
  private void removeInvocationName(Instance instance, String invocationName, HashSet<Instance> removed) {
    if (removed.contains(instance)) {
      return;
    }
    removed.add(instance);

    instance.getFieldSet().remove(invocationName);
    for (Reference fieldRef : instance.getFields()) {
      removeInvocationName(fieldRef, invocationName, removed);
    }
  }
  
  private List<String> sortSubClasses(String superClass, List<String> subClasses, int maxSubClasses) {
    List<String> sorted = new ArrayList<String>();
    
    // use the frequent ones first
    List<String> freqList = SubClassHack.useFreqSubclasses(superClass);
    if (freqList != null) {
      sorted.addAll(freqList);
    }
    else {
      // find those with simple constructor
      for (int i = 0, size = subClasses.size(); i < size && sorted.size() < maxSubClasses; i++) {
        Class<?> cls = Utils.findClass(subClasses.get(i));
        if (cls != null) {
          boolean easy = false;
          Constructor<?>[] ctors = Utils.getPublicCtors(cls);
          for (int j = 0; j < ctors.length && !easy; j++) {
            easy = ctors[j].getParameterTypes().length == 0;
          }
          if (easy) {
            sorted.add(subClasses.get(i));
          }
        }
      }
      
      // fill the rest
      for (int i = 0, size = subClasses.size(); i < size && sorted.size() < maxSubClasses; i++) {
        if (!sorted.contains(subClasses.get(i))) {
          sorted.add(subClasses.get(i));
        }
      }
    }

    return sorted;
  }

  private void setInstanceLifeTime(Reference refTo, Reference refOri, Instance instanceTo, Instance instanceOri, Long invokeTime) {
    if (invokeTime != null) {
      refTo.resetInstanceLiftTime(instanceTo, invokeTime, Long.MAX_VALUE /* not useful in Summary */);
    }
    else {
      Long[] lifeTime = refOri.getLifeTime(instanceOri);
      if (lifeTime != null) {
        refTo.resetInstanceLiftTime(instanceTo, lifeTime[0], Long.MAX_VALUE /* not useful in Summary */);
      }
    }
  }
  
  private void printStepSpaces(int step) {
    for (int j = 0; j < step; j++) {
      System.out.print(">>");
    }
  }
  
  // cannot do starting from a particular method id, because we need 
  // to reuse the extracted method summaries. Use extractedListFile.
  @SuppressWarnings("deprecation")
  public void extractAllMethods(long maxExtractTime, String allMethodsFile, 
      String extractListFile, String filterFile, String extractedListFile) throws Exception {
    
    long start = System.currentTimeMillis();

    // read the full method list
    HashSet<String> allMethodSet = Utils.readStringSetFromFile(allMethodsFile);
    
    // read the list of to extract methods
    List<String> methodsToExtract = Utils.readStringListFromFile(extractListFile);
    
    // read the list of filter methods
    HashSet<String> filterSet = Utils.readStringSetFromFile(filterFile);
    
    // read the list of extracted methods
    HashSet<String> extractedSet = Utils.readStringSetFromFile(extractedListFile);
    
    System.out.println(methodsToExtract.size() + " methods to extract...");

    // extract all methods
    List<String> fullExtractList    = new ArrayList<String>();
    List<String> partialExtractList = new ArrayList<String>();
    List<String> failedExtractList  = new ArrayList<String>();
    BufferedWriter writer0 = new BufferedWriter(new FileWriter("./summaries/summary_progress.txt", false));
    BufferedWriter writer1 = new BufferedWriter(new FileWriter("./summaries/full_extract_methods.txt", false));
    BufferedWriter writer2 = new BufferedWriter(new FileWriter("./summaries/partial_extract_methods.txt", false));
    BufferedWriter writer3 = new BufferedWriter(new FileWriter("./summaries/failed_extract_methods.txt", false));
    for (int i = 0, size = methodsToExtract.size(); i < size; i++) {
      String methodSig = methodsToExtract.get(i);
      
      System.out.println("Method (" + (i + 1) + " / " + size + "): " + methodSig);
      writer0.append(String.valueOf((i + 1))).append(": ").append(methodSig).append("...").flush();
      
      int lastStatus = -1;
      long start2 = System.currentTimeMillis();
      
      try {
        boolean filtered = filterSet.contains(methodSig);
        if (!extractedSet.contains(methodSig) && !filtered) {
          SummaryExtractionThread thread = new SummaryExtractionThread(
              this, methodSig, maxExtractTime, allMethodSet, filterSet, extractedSet);
          thread.start();
          
          long maxExtractTime2 = (long) (maxExtractTime * 10);
          while (thread.isAlive() && (System.currentTimeMillis() - start2) < maxExtractTime2) {
            Thread.sleep(25);
          }
          
          // stop long run methods
          boolean isLongRun = thread.isAlive();
          if (isLongRun) {
            thread.stop();
            List<Summary> extracted = m_summaryDatabase.readSummaries(methodSig);
            lastStatus = (extracted == null || extracted.size() == 0) ? -1 : 0; // failed or partial
          }
          else {
            lastStatus = s_lastStatus;
          }
        }
        else if (filtered) {
          lastStatus = -1;
        }
        else {
          lastStatus = 1;
        }
      } catch (Exception e) {
        e.printStackTrace();
        lastStatus = -1;
      }

      String result = null;
      switch (lastStatus) {
      case -1:
        result = "failed to extract!";
        failedExtractList.add(methodSig);
        writer3.append(methodSig + "\n").flush();
        break;
      case 0:
        result = "partially extracted!";
        partialExtractList.add(methodSig);
        writer2.append(methodSig + "\n").flush();
        break;
      case 1:
        result = "fully extracted!";
        fullExtractList.add(methodSig);
        writer1.append(methodSig + "\n").flush();
        break;
      default:
        break;
      }
      
      // save progress
      writer0.append(result).append(" (")
            .append(String.valueOf(fullExtractList.size())).append(" / ")
            .append(String.valueOf(partialExtractList.size())).append(" / ")
            .append(String.valueOf(failedExtractList.size())).append(")")
            .append(" Total elapsed: ").append(String.valueOf(System.currentTimeMillis() - start2)).append(" ms\n").flush();
    }
    
    String endMsg = "Total elapsed: " + ((System.currentTimeMillis() - start) / 1000) + "s!";
    System.out.println(endMsg);
    writer0.append(endMsg + "\n").flush();
    
    writer0.close();
    writer1.close();
    writer2.close();
    writer3.close();
  }
  
  public SummaryDatabase getSummaryDatabase() {
    return m_summaryDatabase;
  }
  
  public WalaAnalyzer getWalaAnalyzer() {
    return m_walaAnalyzer;
  }
  
  public SMTChecker getSMTChecker() {
    return m_smtChecker;
  }

  public static void main(String args[]) throws Exception {
    if (args.length == 0) {
      //String appJar = "D:/Projects/BranchModelGenerator/targets/apache-commons-collections/target/commons-collections-3.2.1.jar";
      //String appJar = "D:/Projects/BranchModelGenerator/targets/sat4j/target/org.sat4j.core-2.2.0.jar";
      //String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-ant/targets/ant-all-1.7.0_removed.jar";
      //String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-log4j/targets/log4j-1.2.15_removed.jar";
      String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-commons-collections/targets/commons-collections-3.1.jar";
      //String appJar = "D:/Projects/ObjectGen/hk.ust.cse.ObjectGen.jar";
      String pseudoImplJar = "./lib/hk.ust.cse.Prevision_PseudoImpl.jar";
      SummaryExtractor extractor = new SummaryExtractor(appJar, pseudoImplJar);

      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList.<init>(Ljava/util/Collection;)V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.getLeftSubTree()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.getRightSubTree()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.getOffset(Lorg/apache/commons/collections/list/TreeList$AVLNode;)I");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.setOffset(Lorg/apache/commons/collections/list/TreeList$AVLNode;I)I");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.recalcHeight()V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.setLeft(Lorg/apache/commons/collections/list/TreeList$AVLNode;Lorg/apache/commons/collections/list/TreeList$AVLNode;)V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.setRight(Lorg/apache/commons/collections/list/TreeList$AVLNode;Lorg/apache/commons/collections/list/TreeList$AVLNode;)V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.rotateLeft()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.rotateRight()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.balance()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.min()Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.max()Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.removeMax()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.removeMin()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.removeSelf()Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.remove(I)Lorg/apache/commons/collections/list/TreeList$AVLNode");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList.get(I)Ljava/lang/Object;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList.remove(I)Ljava/lang/Object;");
      IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.insert(ILjava/lang/Object;)Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.insertOnLeft(ILjava/lang/Object;)Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.insertOnRight(ILjava/lang/Object;)Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList.add(ILjava/lang/Object;)V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList.listIterator()Ljava/util/ListIterator;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.next()Lorg/apache/commons/collections/list/TreeList$AVLNode;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$TreeListIterator.hasNext()Z");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$TreeListIterator.checkModCount()V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$TreeListIterator.next()Ljava/lang/Object;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.iterators.ObjectGraphIterator.findNextByIterator(Ljava/util/Iterator;)V");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.iterators.ObjectGraphIterator.next()Ljava/lang/Object;");
      //IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.sat4j.minisat.constraints.cnf.LearntHTClause.<init>(Lorg/sat4j/specs/IVecInt;Lorg/sat4j/minisat/core/ILits;)V");
      
      // read the list of all/filter/extracted methods
      HashSet<String> allMethodSet = Utils.readStringSetFromFile("./summaries/all_methods.txt");
      HashSet<String> filterSet    = Utils.readStringSetFromFile("./summaries/filter_methods.txt");
      HashSet<String> extractedSet = Utils.readStringSetFromFile("./summaries/extracted_methods.txt");
      
      long start = System.currentTimeMillis();
      
      String methodSig = ir.getMethod().getSignature();
      List<Summary> extracted = extractor.extract(methodSig, true, 100000, allMethodSet, filterSet, extractedSet);
      
      if (extracted != null) {
        // display summaries
        for (int i = 0, size = extracted.size(); i < size; i++) {
          System.out.println("Summary " + (i + 1) + ": =================================");
          System.out.println(extracted.get(i));
          System.out.println();
        }
        
        // save using summary database
        extractor.getSummaryDatabase().saveSummariesOverride(methodSig, extracted);
        List<Summary> readSummaries = extractor.getSummaryDatabase().refreshCache(methodSig);
        for (int i = 0, size = readSummaries.size(); i < size; i++) {
          System.out.println("Read Summary " + (i + 1) + ": =================================");
          System.out.println(readSummaries.get(i));
          System.out.println();
        }
      }
      System.out.println("Total elapsed: " + (System.currentTimeMillis() - start) + "ms.");
      
//      System.out.println("Total methods extracted and saved: " + extractedSet.size());
//      for (String savedExtraction : extractedSet) {
//        System.out.println(savedExtraction);
//      }
    }
    else {
      SummaryExtractor extractor = new SummaryExtractor(args[0], args[1]);
      extractor.extractAllMethods(Integer.parseInt(args[2]), args[3], args[4], args[5], args[6]);
    }
  }
  
  private final SummaryDatabase       m_summaryDatabase;
  private final IntraSummaryExtractor m_intraExtractor;
  private final WalaAnalyzer          m_walaAnalyzer;
  private final SMTChecker            m_smtChecker;

  private static int s_lastStatus;
}
