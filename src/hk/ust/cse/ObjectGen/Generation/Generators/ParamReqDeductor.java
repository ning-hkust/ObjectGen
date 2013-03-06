package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Requirements;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.Prevision.PathCondition.AndConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.PathCondition.Formula.SMT_RESULT;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.VirtualMachine.AbstractMemory;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Instance.INSTANCE_OP;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision.VirtualMachine.Relation;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class ParamReqDeductor {

  public ParamReqDeductor(IR ir, boolean isFactoryOrCreateInner, ObjectGenerator objGenerator) {
    m_ir                     = ir;
    m_isFactoryOrCreateInner = isFactoryOrCreateInner;
    m_objGenerator           = objGenerator;
    m_smtChecker             = objGenerator.getSMTChecker();
    m_walaAnalyzer           = objGenerator.getWalaAnalyzer();
    m_moreValuesLower        = objGenerator.getFindMoreValues()[0];
    m_moreValuesHigher       = objGenerator.getFindMoreValues()[1];
  }
  
  // compute the necessary requirements on the parameters
  public DeductResult deductChildReqs(Summary summary, Requirement req) {
    Requirements childReqs = null;
    Variable keyVariable   = null; // the key variable which will satisfy req after executing the target method
    boolean returnValIsKey = false;

    // encode 1) summary path condition + 2) summary effect + 3) requirement conditions
    Object[] created = createValidatingFormula(summary, req);
    Formula validateFormula = (Formula) created[0];
    SMT_RESULT result = m_smtChecker.smtCheck(validateFormula, false, true, false, true, true, true);
    if (!result.equals(SMT_RESULT.SAT)) {
      return null;
    }
    
    // parse satModel from (field @ 21474836472) to v1.field
    List<Condition> newConditionList = new ArrayList<Condition>();
    List<BinaryConditionTerm> nonParamTerms = new ArrayList<BinaryConditionTerm>();
    keyVariable = parseSatModel(m_smtChecker.getLastResult().getSatModel(), 
        newConditionList, nonParamTerms, req.getTargetInstance() != null, validateFormula);
    
    // target does not come from any of the param, so it should come from RET or we do not need it
    if (keyVariable == null && !m_ir.getMethod().getReturnType().getName().toString().equals("V")) {
      keyVariable = new Variable(m_objGenerator.nextVariableName(), req.getTargetInstance().getLastRefType());
      returnValIsKey = true;
    }
    
    // no way we can satisfy them because they are not parameters
    if (nonParamTerms.size() > 0) {
      return null;
    }

    Class<?> reqTargetType = req.getTargetType();
    boolean v1UsesInnerClass = req.getUseInnerClass() || (!returnValIsKey && 
                               ((!m_ir.getMethod().isStatic() && m_ir.getMethod().isProtected()) || 
                               ((Modifier.isProtected(reqTargetType.getModifiers()) || 
                                 Modifier.isAbstract(reqTargetType.getModifiers())) && m_ir.getMethod().isInit())));
    
    // try to obtain more values for integer type instances
    newConditionList = findMoreValuesAll(newConditionList, summary, req, m_moreValuesLower, m_moreValuesHigher);
    
    // ArrayList/Vector.elementData.length hack: Since solver only outputs one model, 
    // thus limiting the elementData.length field to a particular value. However, in 
    // reality, elementData.length can always be handled properly by ArrayList/Vector, 
    // thus, we manual set the value to 10 so that the simple constructor can be used.
    for (int i = 0, size = newConditionList.size(); i < size; i++) {
      Condition condition = newConditionList.get(i);
      if (condition.getConditionTerms().size() == 1) {
        ConditionTerm term = condition.getConditionTerms().get(0);
        if (term instanceof BinaryConditionTerm) {
          BinaryConditionTerm newTerm = Requirements.elementDataLengthHack((BinaryConditionTerm) term);
          if (newTerm != term) {
            newConditionList.set(i, new Condition(newTerm));
          }
        }
      }
    }
    
    // split model by parameter and form multiple requirements
    childReqs = splitModel(newConditionList, v1UsesInnerClass);
    
    // if the method is <init>, make sure we have no more requirements for v1
    boolean canEndByCtor = false;
    if (m_ir.getMethod().isInit()) {
      Requirement v1Req = childReqs.getRequirement("v1");
      canEndByCtor = v1Req == null || m_objGenerator.onlyVarNotNullReq(v1Req);
      if (canEndByCtor) {
        childReqs.removeRequirement("v1"); // we don't want endless recursion
      }
    }
    if (m_ir.getMethod().isInit() && !canEndByCtor) {
      return null;
    }
    
    return new DeductResult(childReqs, keyVariable, returnValIsKey, canEndByCtor);
  }
  
  private Object[] createValidatingFormula(Summary summary, Requirement req) {
    // create a formula
    Hashtable<String, Reference> effect = summary.getEffect();
    
    Hashtable<String, Instance> readFieldMap  = new Hashtable<String, Instance>();
    Hashtable<String, Relation> relationMap   = new Hashtable<String, Relation>();
    Hashtable<Instance, Instance> instanceMap = new Hashtable<Instance, Instance>();
    
    // add references to refMap
    Hashtable<String, Hashtable<String, Reference>> refMap = new Hashtable<String, Hashtable<String, Reference>>();
    Hashtable<String, Reference> refMap2 = new Hashtable<String, Reference>();
    for (int i = 1; i <= summary.getMethodData().getParamList().size(); i++) {
      Reference reference = effect.get("v" + i);
      refMap2.put("v" + i, reference);
    }
    
    // add static field classes, e.g. Lorg/apache/log4j/NDC
    Enumeration<String> keys = effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      if (key.startsWith("L")) {
        Reference reference = effect.get(key);
        refMap2.put(key, reference);
      }
    }
    refMap.put("", refMap2);

    // update relations to reflect summary effect (relationMap)
    Hashtable<String, String> readRelNameMap = new Hashtable<String, String>();
    Hashtable<String, Relation> summaryRelationMap = summary.getRelationMap();
    keys = summaryRelationMap.keys();
    while (keys.hasMoreElements()) {
      String relName = (String) keys.nextElement();
      updateRelation(relationMap, readFieldMap, summaryRelationMap.get(relName), readRelNameMap);
    }
    
    // add path conditions of the summary before updating effect (precondition)
    List<Condition> conditionList = new ArrayList<Condition>();
    for (Condition condition : summary.getPathConditions()) {
      List<ConditionTerm> condTerms = new ArrayList<ConditionTerm>();
      for (ConditionTerm term : condition.getConditionTerms()) {
        ConditionTerm condTerm = null;
        if (term instanceof BinaryConditionTerm) {
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
          Instance instance1 = toRelationInstance(relationMap, readFieldMap, binaryTerm.getInstance1(), readRelNameMap);
          Instance instance2 = toRelationInstance(relationMap, readFieldMap, binaryTerm.getInstance2(), readRelNameMap);
          condTerm = new BinaryConditionTerm(instance1, binaryTerm.getComparator(), instance2);
          instanceMap.put(binaryTerm.getInstance1(), instance1);
          instanceMap.put(binaryTerm.getInstance2(), instance2);
        }
        else if (term instanceof TypeConditionTerm) {
          TypeConditionTerm typeTerm = (TypeConditionTerm) term;
          Instance instance1 = toRelationInstance(relationMap, readFieldMap, typeTerm.getInstance1(), readRelNameMap);
          condTerm = new TypeConditionTerm(instance1, typeTerm.getComparator(), typeTerm.getTypeString());
          instanceMap.put(typeTerm.getInstance1(), instance1);
        }
        condTerms.add(condTerm);
      }
      conditionList.add(new Condition(condTerms));
    }

    // update relations to reflect summary effect (effect)
    // 1) parameters
    for (int i = 1; i <= summary.getMethodData().getParamList().size(); i++) {
      Reference reference = effect.get("v" + i);
      updateRelation(relationMap, readFieldMap, reference, readRelNameMap, 0, 10);
    }
    // 2) static fields
    keys = effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      if (key.startsWith("L")) {
        Reference reference = effect.get(key);
        updateRelation(relationMap, readFieldMap, reference, readRelNameMap, 0, 10);
      }
    }
    // 3) fields in FreshInstances
    keys = summaryRelationMap.keys();
    while (keys.hasMoreElements()) {
      String relName = (String) keys.nextElement();
      updateRelationForHiddenFresh(relationMap, readFieldMap, summaryRelationMap.get(relName), readRelNameMap);
    }
    // 4) return value
    if (effect.containsKey("RET")) {
      Reference reference = effect.get("RET");
      updateRelation(relationMap, readFieldMap, reference, readRelNameMap, 0, 10);
    }
    
    // we do not want to use the reads coming from before update
    readFieldMap.clear();
    
    // add requirement condition: target == v1 or v2 or ... or RET (postcondition)
    if (req.getTargetInstance() != null) {
      BinaryConditionTerm term = null;
//      String methodSig = summary.getMethodData().getMethodSignature();
//      if (!methodSig.startsWith("hk.ust.cse.Prevision_PseudoImpl.Map.put") && 
//          !methodSig.startsWith("hk.ust.cse.Prevision_PseudoImpl.Table.put")) {
//        // target == v1 or v2 or ... or RET (postcondition)
//        for (int i = 1; i <= summary.getMethodData().getParamList().size(); i++) {
//          Reference reference = effect.get("v" + i);
//          ConditionTerm term = new BinaryConditionTerm(
//              req.getTargetInstance(), Comparator.OP_EQUAL, reference.getInstance());
//          terms.add(term);
//        }
//        
//        if (effect.containsKey("RET")) { // this invocation does not return void
//          Reference reference = effect.get("RET");
//          Instance retInstance = toRelationInstance(relationMap, readFieldMap, reference.getInstance(), readRelNameMap);
//          ConditionTerm term = new BinaryConditionTerm(
//              req.getTargetInstance(), Comparator.OP_EQUAL, retInstance);
//          terms.add(term);
//        }
//      }
//      else {
      if (!summary.getMethodData().isStatic() && !m_isFactoryOrCreateInner) {
        // only allow target == v1
        Reference reference = effect.get("v1");
        term = new BinaryConditionTerm(req.getTargetInstance(), Comparator.OP_EQUAL, reference.getInstance());
        
        // set to real type
        reference.setType(req.getTargetInstance().getLastRefType());
      }
      else if (effect.containsKey("RET")) { // this invocation does not return void
        Reference reference = effect.get("RET");
        Instance retInstance = toRelationInstance(relationMap, readFieldMap, reference.getInstance(), readRelNameMap);
        term = new BinaryConditionTerm(req.getTargetInstance(), Comparator.OP_EQUAL, retInstance);
        instanceMap.put(reference.getInstance(), retInstance);
      }
//      }
      if (term != null) {
        conditionList.add(new Condition(term));
      }
    }

    // add other requirement conditions from req (postcondition)
    int sizeBeforeReqConds = conditionList.size();
    Hashtable<String, HashSet<Instance>> typeInstanceMap = new Hashtable<String, HashSet<Instance>>();
    Hashtable<Integer, List<ConditionTerm>> multiModelCombs = new Hashtable<Integer, List<ConditionTerm>>();
    for (BinaryConditionTerm reqTerm : req.getRequirementTerms()) {
      Instance instance1 = toRelationInstance(relationMap, readFieldMap, reqTerm.getInstance1(), readRelNameMap); // target.size
      Instance instance2 = toRelationInstance(relationMap, readFieldMap, reqTerm.getInstance2(), readRelNameMap); // #!5
      instanceMap.put(reqTerm.getInstance1(), instance1);
      instanceMap.put(reqTerm.getInstance2(), instance2);

      // contain multiple model values, e.g.: v1.size == #!1|#!2, v1.data.length == #!1|#!2
      if (instance2.getValue().startsWith("#!") && instance2.getValue().contains("|")) {
        splitMultiModelValues(multiModelCombs, instance1, reqTerm.getComparator(), instance2);
      }
      else {
        conditionList.add(new Condition(new BinaryConditionTerm(instance1, reqTerm.getComparator(), instance2)));
      }
      
      // add type condition term for field access and array elements
      TypeConditionTerm typeTerm = null;
      if (reqTerm.getComparator().equals(BinaryConditionTerm.Comparator.OP_INEQUAL) && 
          instance2.getValue() != null && instance2.getValue().equals("null")) {
        
        String type = null;
        if (reqTerm.getInstance1().getLastReference() != null) { // field access
          type = reqTerm.getInstance1().getLastRefType();
          typeTerm = new TypeConditionTerm(instance1, TypeConditionTerm.Comparator.OP_INSTANCEOF, type);
        }
        else if (reqTerm.getInstance1().getRight() != null && reqTerm.getInstance1().getType() != null) { // array access
          type = reqTerm.getInstance1().getType();
          typeTerm = new TypeConditionTerm(instance1, TypeConditionTerm.Comparator.OP_INSTANCEOF, type);
        }

        // collect instances with not null condition
        if (type != null) {
          HashSet<Instance> instances = typeInstanceMap.get(type);
          if (instances == null) {
            instances = new HashSet<Instance>();
            typeInstanceMap.put(type, instances);
          }
          instances.add(instance1);
        }
      }
      
      if (typeTerm != null) {
        conditionList.add(new Condition(typeTerm));
      }
    }
    
    // add the multiple model combinations as AndConditionTerms
    List<ConditionTerm> terms = new ArrayList<ConditionTerm>();
    Enumeration<Integer> keys2 = multiModelCombs.keys();
    while (keys2.hasMoreElements()) {
      Integer key2 = (Integer) keys2.nextElement();
      terms.add(new AndConditionTerm(multiModelCombs.get(key2)));
    }
    conditionList.add(new Condition(terms));

    // remove unnecessary updates obtained from summary
    removeUselessUpdates(conditionList, sizeBeforeReqConds, relationMap);
    
    HashSet<Instance> usedInstances = findUsedInstances(conditionList, sizeBeforeReqConds, relationMap);
    
    // add same type not equal conditions
    keys = typeInstanceMap.keys();
    while (keys.hasMoreElements()) {
      String type = (String) keys.nextElement();
      HashSet<Instance> instances = typeInstanceMap.get(type);
      List<Instance> instanceList = new ArrayList<Instance>(instances);
      for (int i = 0, size = instanceList.size(); i < size; i++) {
        Instance instance1 = instanceList.get(i);
        if (usedInstances.contains(instance1)) {
          for (int j = i + 1; j < size; j++) {
            Instance instance2 = instanceList.get(j);
            if (usedInstances.contains(instance2)) {
              if (instance1 != instance2 && !instance1.toString().equals(instance2.toString())) {
                BinaryConditionTerm condTerm = new BinaryConditionTerm(instance1, Comparator.OP_INEQUAL, instance2);
                conditionList.add(new Condition(condTerm));
              }
            }
          }
        }
      }
    }
    
    // add parameters not equal conditions (especially useful when one parameter is a super class of another)
    Instance nullInstance = new Instance("null", "", null);
    for (int i = 1; i <= summary.getMethodData().getParamList().size(); i++) {
      Instance instance1 = effect.get("v" + i).getInstance();
      if (usedInstances.contains(instance1)) {
        if (!Utils.isPrimitiveType(instance1.getLastRefType())) {
          for (int j = i + 1; j <= summary.getMethodData().getParamList().size(); j++) {
            Instance instance2 = effect.get("v" + j).getInstance();
            if (usedInstances.contains(instance2)) {
              if (!Utils.isPrimitiveType(instance2.getLastRefType())) {
                if (!instance1.toString().equals(instance2.toString())) {
                  List<ConditionTerm> condTerms = new ArrayList<ConditionTerm>();
                  condTerms.add(new BinaryConditionTerm(instance1, Comparator.OP_EQUAL, nullInstance));
                  condTerms.add(new BinaryConditionTerm(instance2, Comparator.OP_EQUAL, nullInstance));
                  condTerms.add(new BinaryConditionTerm(instance1, Comparator.OP_INEQUAL, instance2));
                  conditionList.add(new Condition(condTerms));
                }
              }
            }
          }
        }
      }
    }
    
    // translate to Formula
    Formula formula = new Formula(conditionList, new AbstractMemory(refMap, null, relationMap));
    return new Object[] {formula, instanceMap};
  }
  
  private HashSet<Instance> findUsedInstances(List<Condition> conditionList, 
      int sizeBeforeReqConds, Hashtable<String, Relation> relationMap) {

    // find all instances used in path condition
    HashSet<Instance> used = new HashSet<Instance>();
    for (int i = 0, size = conditionList.size(); i < size && i < sizeBeforeReqConds; i++) {
      Condition condition = conditionList.get(i);
      findUsedInstances(condition.getConditionTerms(), used);
    }
    
    // find all instances used in effect update
    findUsedInstances(relationMap, used);
    
    return used;
  }
  
  private void findUsedInstances(List<ConditionTerm> terms, HashSet<Instance> usedInstances) {
    for (ConditionTerm term : terms) {
      if (term instanceof TypeConditionTerm || term instanceof BinaryConditionTerm) {
        usedInstances.addAll(Arrays.asList(term.getInstances()));
      }
      else if (term instanceof AndConditionTerm) {
        List<ConditionTerm> andTerms = ((AndConditionTerm) term).getAndConditionTerms();
        findUsedInstances(andTerms, usedInstances);
      }
    }
  }
  
  private void findUsedInstances(Hashtable<String, Relation> relationMap, HashSet<Instance> usedInstances) {
    Enumeration<String> fieldNames = relationMap.keys();
    while (fieldNames.hasMoreElements()) {
      String fieldName = (String) fieldNames.nextElement();
      Relation relation = relationMap.get(fieldName);
      for (int i = 0; i < relation.getFunctionCount(); i++) {
        if (relation.getRangeValues().get(i) != null /* an update */ ) {
          Instance usedInstance = relation.getRangeValues().get(i);
          usedInstances.add(usedInstance);
        }
      }
    }
  }
  
  private void removeUselessUpdates(List<Condition> conditionList, 
      int sizeBeforeReqConds, Hashtable<String, Relation> relationMap) {
    
    // find all field names referred by target goal state
    HashSet<String> targetUsedFieldNames = new HashSet<String>();
    for (int i = sizeBeforeReqConds, size = conditionList.size(); i < size; i++) {
      Condition condition = conditionList.get(i);
      HashSet<String> readFieldNames = new HashSet<String>();
      getRelatedFieldNames(condition.getConditionTerms(), readFieldNames, relationMap);
      targetUsedFieldNames.addAll(readFieldNames);
    }

    // remove the updates to field names that are not used as they are not important
    Enumeration<String> fieldNames = relationMap.keys();
    while (fieldNames.hasMoreElements()) {
      String fieldName = (String) fieldNames.nextElement();
      if (!targetUsedFieldNames.contains(fieldName)) {
        Relation relation = relationMap.get(fieldName);
        for (int i = 0; i < relation.getFunctionCount(); i++) {
          if (relation.getRangeValues().get(i) != null /* an update */ ) {
            relation.remove(i--);
          }
        }
      }
    }
  }
  
  private void getRelatedFieldNames(List<ConditionTerm> terms, 
      HashSet<String> readFieldNames, Hashtable<String, Relation> relationMap) {
    
    for (ConditionTerm term : terms) {
      if (term instanceof TypeConditionTerm || term instanceof BinaryConditionTerm) {
        Instance[] instances = term.getInstances();
        for (Instance instance : instances) {
          getRelatedFieldNames(instance, readFieldNames, relationMap);
        }
      }
      else if (term instanceof AndConditionTerm) {
        List<ConditionTerm> andTerms = ((AndConditionTerm) term).getAndConditionTerms();
        getRelatedFieldNames(andTerms, readFieldNames, relationMap);
      }
    }
  }
  
  private void getRelatedFieldNames(Instance instance, 
      HashSet<String> readFieldNames, Hashtable<String, Relation> relationMap) {
    
    if (instance.isRelationRead()) {
      String str = instance.toString();
      String fieldName = Relation.getReadStringRelName(str);
      if (fieldName != null) {
        readFieldNames.add(fieldName);

        Relation rel = relationMap.get(fieldName);
        int index = rel.getIndex(Relation.getReadStringTime(str));
        if (index >= 0) {
          Instance[] domains = rel.getDomainValues().get(index);
          for (Instance domain : domains) {
            getRelatedFieldNames(domain, readFieldNames, relationMap);
          }
        }
      }
    }
  }
  
  private void splitMultiModelValues(Hashtable<Integer, List<ConditionTerm>> multiModelCombs, Instance instance1, 
      BinaryConditionTerm.Comparator comparator, Instance instance2) {
    
    String[] allModelValues = instance2.getValue().split("\\|");
    for (int i = 0; i < allModelValues.length; i++) {
      List<ConditionTerm> andConditionTerms = multiModelCombs.get(i);
      if (andConditionTerms == null) {
        andConditionTerms = new ArrayList<ConditionTerm>();
        multiModelCombs.put(i, andConditionTerms);
      }
      andConditionTerms.add(new BinaryConditionTerm(instance1, comparator, new Instance(allModelValues[i], "I", null)));
    }
  }
  
  private void updateRelation(Hashtable<String, Relation> relationMap, Hashtable<String, Instance> readFieldMap, 
      Reference reference, Hashtable<String, String> readRelNameMap, int currDepth, int maxDepth) {

    // read/update relation
    Instance instance = reference.getInstance();
    if (reference.getDeclaringInstance() != null) { // v1.next
      if (instance.getLastReference() != reference) { // assign field: v1.next = v2.prev
        Instance fieldInstanceFrom = toRelationInstance(relationMap, readFieldMap, instance, readRelNameMap); // v2.prev
        
        // get relation
        String fieldName = reference.getName(); // next
        
        // convert to array theory format
        String fullFieldName = reference.getLongName(); // v1.next
        Relation relation = relationMap.get(fieldName);
        if (relation == null) {
          relation = new Relation(fieldName, 1, true);
          relationMap.put(fieldName, relation);
        }
        
        // save the current instance before update
        Instance parent = toRelationInstance(
            relationMap, readFieldMap, reference.getDeclaringInstance(), readRelNameMap); // v1
        if (!readFieldMap.containsKey(fullFieldName)) {
          Reference relationRef = relation.read(new Instance[] {parent}, reference.getType(), null);
          readFieldMap.put(fullFieldName, relationRef.getInstance());     
        }
        
        // a trick to avoid meaningless updates
        if (!alreadyUpdated(relation, parent)) {
          relation.update(new Instance[] {parent}, fieldInstanceFrom);
        }
      }
    }

    if (currDepth < maxDepth) { // avoid endless recursion, e.g., v1.header.before = v1.header
      //if (instance.getLastReference() == reference) {
        Collection<Reference> fieldRefs = instance.getFields();
        for (Reference fieldRef : fieldRefs) {
          if (!fieldRef.getName().contains("(") && 
              !fieldRef.getName().matches("v[0-9]+_[v#][\\S]+")) { // _undecidable_ for param var, invocation string for ref var
            updateRelation(relationMap, readFieldMap, fieldRef, readRelNameMap, currDepth + 1, maxDepth);
          }
        }
      //}
    }
  }
  
  // a trick to avoid meaningless updates
  private boolean alreadyUpdated(Relation relation, Instance parent) {
    boolean alreadyUpdated = false;
    for (int i = relation.getFunctionCount() - 1; i >= 0 && !alreadyUpdated; i--) {
      if (relation.getRangeValues().get(i) != null) { // update
        alreadyUpdated = parent == relation.getDomainValues().get(i)[0];
      }
    }
    return alreadyUpdated;
  }
  
  private void updateRelation(Hashtable<String, Relation> relationMap, 
      Hashtable<String, Instance> readFieldMap, Relation summaryRelation, Hashtable<String, String> readRelNameMap) {
    
    String relName = summaryRelation.getName();
    Relation relation = relationMap.get(relName);
    if (relation == null) {
      relation = new Relation(relName, summaryRelation.getDomainDimension(), summaryRelation.getDirection());
      relationMap.put(relName, relation);
    }
    
    for (int i = 0, size = summaryRelation.getFunctionCount(); i < size; i++) {
      Instance[] domainValues = summaryRelation.getDomainValues().get(i);
      Instance[] relDomainValues = new Instance[domainValues.length];
      for (int j = 0; j < domainValues.length; j++) {
        relDomainValues[j] = toRelationInstance(relationMap, readFieldMap, domainValues[j], readRelNameMap);
      }
      
      if (summaryRelation.getRangeValues().get(i) == null) {
        Reference readRef = relation.read(relDomainValues, "", null);
        readRelNameMap.put("read_" + relName + "_" + summaryRelation.getFunctionTimes().get(i), readRef.getName());
      }
      else {
        Instance rangeValue = summaryRelation.getRangeValues().get(i);
        Instance relRangeValue = toRelationInstance(relationMap, readFieldMap, rangeValue, readRelNameMap);
        relation.update(relDomainValues, relRangeValue);
      }
    }
  }
  
  // in case we have assigned a FreshInstance to an array element, we 
  // need to also put in the effects of this FreshInstance's fields.
  private void updateRelationForHiddenFresh(Hashtable<String, Relation> relationMap, 
      Hashtable<String, Instance> readFieldMap, Relation summaryRelation, Hashtable<String, String> readRelNameMap) {

    for (int i = 0, size = summaryRelation.getFunctionCount(); i < size; i++) {
      if (summaryRelation.getRangeValues().get(i) != null) { // an update
        Instance rangeValue = summaryRelation.getRangeValues().get(i);
        if (rangeValue.getValue() != null && rangeValue.getValue().startsWith("FreshInstanceOf")) {
          Collection<Reference> fieldRefs = rangeValue.getFields();
          for (Reference fieldRef : fieldRefs) { // the field assignments in this FreshInstance are also effects!
            if (!fieldRef.getName().contains("(") && 
                !fieldRef.getName().matches("v[0-9]+_[v#][\\S]+")) { // _undecidable_ for param var, invocation string for ref var
              updateRelation(relationMap, readFieldMap, fieldRef, readRelNameMap, 0, 10);
            }
          }
        }
      }
    }
  }
  
  private Instance toRelationInstance(Hashtable<String, Relation> relationMap, Hashtable<String, Instance> readFieldMap, 
      Instance nonRelationInstance, Hashtable<String, String> readRelNameMap) {
    
    Instance relationInstance = null;
    if (!nonRelationInstance.isBounded()) { // field access
      if (nonRelationInstance.getLastReference().getDeclaringInstance() != null) { // v1.field
        String fieldName = nonRelationInstance.getLastRefName();
        String fullFieldName = nonRelationInstance.getLastReference().getLongName();
        
        // may be already read before
        relationInstance = readFieldMap.get(fullFieldName);
        if (relationInstance == null) {
          Relation relation = relationMap.get(fieldName);
          if (relation == null) {
            relation = new Relation(fieldName, 1, true);
            relationMap.put(fieldName, relation);
          }
          
          // perform relation.read(parentInstance)
          Instance parent = toRelationInstance(relationMap, readFieldMap, 
              nonRelationInstance.getLastReference().getDeclaringInstance(), readRelNameMap);
          
          Reference relationRef = relation.read(new Instance[] {parent}, nonRelationInstance.getLastRefType(), null);
          relationInstance = relationRef.getInstance();
          readFieldMap.put(fullFieldName, relationInstance);
        }
      }
      else if (!nonRelationInstance.getLastRefName().startsWith("read_")) { // v1
        relationInstance = nonRelationInstance;
      }
      else { // read_@@array_11111111
        String readStr = nonRelationInstance.getLastRefName();
        String newReadStr = readRelNameMap.get(readStr);
        if (newReadStr != null) {
          Reference oldReadRef = nonRelationInstance.getLastReference();
          Reference newReadRef = new Reference(newReadStr, oldReadRef.getType(), oldReadRef.getCallSites(), 
              new Instance("", nonRelationInstance.getCreateBlock()), null, true);
          relationInstance = newReadRef.getInstance();
          // need to put to effect?
        }
      }
    }
    else if (!nonRelationInstance.isAtomic()) { // left op right
      if (nonRelationInstance.getOp() != INSTANCE_OP.DUMMY) {
        Instance left  = toRelationInstance(relationMap, readFieldMap, nonRelationInstance.getLeft(), readRelNameMap);
        Instance right = toRelationInstance(relationMap, readFieldMap, nonRelationInstance.getRight(), readRelNameMap);
        relationInstance = new Instance(left, nonRelationInstance.getOp(), right, null);
      }
      else { // array access
        Instance left  = toRelationInstance(relationMap, readFieldMap, nonRelationInstance.getLeft(), readRelNameMap);
        Instance right = toRelationInstance(relationMap, readFieldMap, nonRelationInstance.getRight(), readRelNameMap);

        Relation relation = relationMap.get("@@array");
        if (relation == null) {
          relation = new Relation("@@array", 2, true);
          relationMap.put("@@array", relation);
        }
        
        // perform relation.read(parentInstance)
        String typeName = nonRelationInstance.getLeft().getLastRefType();
        typeName = typeName.startsWith("[") ? typeName.substring(1) : typeName;
        Reference relationRef = relation.read(new Instance[] {left, right}, typeName, null);
        relationInstance = relationRef.getInstance();
      }
    }
    else {
      relationInstance = nonRelationInstance;
    }

    return relationInstance;
  }
  

  private Variable parseSatModel(List<ConditionTerm> satModel, List<Condition> newConditionList, 
      List<BinaryConditionTerm> nonParamStaticTerms, boolean findTargetAssignFrom, Formula validateFormula) {

    String targetValue = null;
    Variable targetAssignFrom = null;
    
    // handle typeConditions, collect explicit type information first
    Hashtable<Instance, String> instanceTypeMap = new Hashtable<Instance, String>();
    for (ConditionTerm satModelTerm : satModel) {
      if (!(satModelTerm instanceof TypeConditionTerm)) {
        continue;
      }
      
      TypeConditionTerm typeSatModelTerm = (TypeConditionTerm) satModelTerm;
      instanceTypeMap.put(typeSatModelTerm.getInstance1(), typeSatModelTerm.getTypeString());
    }
    
    // collect all instances which have type constraints on them
    HashSet<Instance> instancesWithTypeTerm = new HashSet<Instance>();
    for (Condition condition : validateFormula.getConditionList()) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        if (term instanceof TypeConditionTerm) {
          instancesWithTypeTerm.add(((TypeConditionTerm) term).getInstance1());
        }
      }
    }
    
    Hashtable<String, List<Object[]>> toConcretizeList = new Hashtable<String, List<Object[]>>();
    Hashtable<Instance, String> toConcretizeList2 = new Hashtable<Instance, String>();
    Hashtable<String, List<Instance[]>> modelValueVarMap = new Hashtable<String, List<Instance[]>>();
    Hashtable<Instance[], Integer> varIndexMap = new Hashtable<Instance[], Integer>();
    Hashtable<Instance, Instance> oldNewInstanceMap = new Hashtable<Instance, Instance>();
    for (int i = 0, size = satModel.size(); i < size && nonParamStaticTerms.size() == 0; i++) {
      ConditionTerm satModelTerm = satModel.get(i);
      if (!(satModelTerm instanceof BinaryConditionTerm)) { // handle typeConditions later
        continue;
      }
      
      BinaryConditionTerm binarySatModelTerm = (BinaryConditionTerm) satModelTerm;
      Instance instance1 = binarySatModelTerm.getInstance1();
      Instance instance2 = binarySatModelTerm.getInstance2();
      if (instance1.getRight() == null) { // (= v1 3)
        Reference lastRef = instance1.getLastReference();
        
        // check if it is a parameter term
        if (validateFormula.getRefMap().get("").get(lastRef.getName()) == null && !lastRef.getName().equals("v9999") && 
           !lastRef.getName().endsWith(".class") && // give a wild card to .class
           !lastRef.getName().startsWith("java.lang.System.") &&  // give a wild card to java.lang.System.
           !lastRef.getName().startsWith("java.lang.Runtime.") && // give a wild card to java.lang.Runtime.
           !lastRef.getName().startsWith("java.lang.Integer.") && // give a wild card to java.lang.Integer.
           !lastRef.getName().startsWith("java.lang.Class.")) { // give a wild card to java.lang.Class.
          // e.g.: java.util.Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;_482682480861585
          nonParamStaticTerms.add(binarySatModelTerm);
          continue;
        }
        
        String varValue = instance2.getValueWithoutPrefix(); // the value from solver
        List<Instance[]> instances = modelValueVarMap.get(varValue);
        if (instances == null) {
          instances = new ArrayList<Instance[]>();
          modelValueVarMap.put(varValue, instances);
        }
        
        // since the SMT solver may give some very specific type to the instance which does
        // not make any sense (just a specific model), we only use this type information under certain conditions
        String typeName = lastRef.getType();
        if (shouldUseModelType(instancesWithTypeTerm, instance1, modelValueVarMap, varValue)) {
          typeName = instanceTypeMap.containsKey(instance1) ? instanceTypeMap.get(instance1) : typeName;
        }
        
        // retrieve the target variable assign from name
        if (findTargetAssignFrom && targetAssignFrom == null) {
          if (lastRef.getName().equals("v9999")) { // default name for target
            targetValue = varValue;
            if (instances.size() > 0) {
              String varName = instances.get(0)[0].getLastRefName();
              String varType = instances.get(0)[0].getLastRefType();
              targetAssignFrom = new Variable(varName, varType);
            }
          }
          else if (varValue.equals(targetValue)) {
            String varName = lastRef.getName();
            targetAssignFrom = new Variable(varName, typeName);
          }
        }

        // re-create a new instance of v1
        Reference reference1 = new Reference(
            lastRef.getName(), typeName, lastRef.getCallSites(), new Instance("", null), null, true);
        // save model value to instance mapping
        Instance[] instancePair = new Instance[]{reference1.getInstance(), instance1};
        instances.add(instancePair);
        varIndexMap.put(instancePair, i);
        oldNewInstanceMap.put(instance1, reference1.getInstance());

        // create instance2
        BinaryConditionTerm term = createConditionRHS(reference1.getInstance(), instance2, typeName);
        newConditionList.add(new Condition(term));
      }
    }
    
    // parse function interpretations: from (= (size 3) 1) to v1.size == 1 as a new condition
    for (int i = 0, size = satModel.size(); i < size && nonParamStaticTerms.size() == 0; i++) {
      ConditionTerm satModelTerm = satModel.get(i);
      if (!(satModelTerm instanceof BinaryConditionTerm)) { // handle typeConditions later
        continue;
      }
      
      BinaryConditionTerm binarySatModelTerm = (BinaryConditionTerm) satModelTerm;
      Instance instance1 = binarySatModelTerm.getInstance1();
      Instance instance2 = binarySatModelTerm.getInstance2();
      if (instance1.getRight() != null && instance1.getOp().equals(INSTANCE_OP.DUMMY)) { // function interpretation: (= (size 3) 1) or (= (@@array 2147483649 0) 2147483649)
        Instance lhsInstance = null;
        String fieldName     = null;
        String objRefValue   = null;
        if (instance1.getLeft().getValue().startsWith("##")) { // field access: (= (size 3) 1)
          fieldName   = instance1.getLeft().getValueWithoutPrefix();
          objRefValue = instance1.getRight().getValueWithoutPrefix();
          
          // later should be assigned as a field referncece's instance
          lhsInstance = new Instance("", null);
        }
        else { // array access: (= (@@array 2147483649 0) 2147483649)
          fieldName   = "@@array";
          objRefValue = instance1.getLeft().getValueWithoutPrefix();
          
          // this is how we represent instance[index]
          lhsInstance = new Instance(null, INSTANCE_OP.DUMMY, instance1.getRight(), null);
        }

        List<Object[]> toConcretize = toConcretizeList.get(objRefValue);
        if (toConcretize == null) {
          toConcretize = new ArrayList<Object[]>();
          toConcretizeList.put(objRefValue, toConcretize);
        }
        toConcretize.add(new Object[] {fieldName, lhsInstance, instance2, binarySatModelTerm});
        toConcretizeList2.put(lhsInstance, objRefValue);
        
        // save model value to instance mapping
        String varValue = instance2.getValueWithoutPrefix(); // the value from solver
        List<Instance[]> instances = modelValueVarMap.get(varValue);
        if (instances == null) {
          instances = new ArrayList<Instance[]>();
          modelValueVarMap.put(varValue, instances);
        }
        Instance[] instancePair = new Instance[]{lhsInstance, instance1};
        instances.add(instancePair);
        varIndexMap.put(instancePair, i);
        oldNewInstanceMap.put(instance1, lhsInstance);
        
        String typeName = instanceTypeMap.get(instance1);
        if (typeName != null) {
          // store the type name for lhsInstance for concretize
          instanceTypeMap.put(lhsInstance, typeName);
        }
      }
    }
    
    // concretize objRef instances according to model values 
    // and create the binary condition terms for them
    HashSet<Object[]> concretized = new HashSet<Object[]>();
    Enumeration<String> keys = toConcretizeList.keys();
    while (keys.hasMoreElements() && nonParamStaticTerms.size() == 0 /* once found nonParamTerms, cannot satisfy anyway */) {
      String modelValue = (String) keys.nextElement();
      List<Object[]> toConcretizes = toConcretizeList.get(modelValue);
      
      for (Object[] toConcretize : toConcretizes) {
        if (!concretized.contains(toConcretize)) {
          HashSet<Object[]> concretizing = new HashSet<Object[]>();
          concretizing.add(toConcretize);
          concretizeModelValue(toConcretize, modelValue, toConcretizeList, toConcretizeList2, modelValueVarMap, varIndexMap, 
              instanceTypeMap, newConditionList, nonParamStaticTerms, concretized, concretizing);
        }
      }
    }
    
    // since we gave a wild card to java.lang.System., remove all related conditions
    for (int i = 0; i < newConditionList.size(); i++) {
      ConditionTerm term = newConditionList.get(i).getConditionTerms().get(0);
      Instance instance1 = term.getInstances()[0];
      
      Instance topInstance = instance1.getToppestInstance();
      while (topInstance.getRight() != null && topInstance.getOp().equals(INSTANCE_OP.DUMMY)) {
        topInstance = topInstance.getLeft();
        topInstance = topInstance.getToppestInstance();
      }
      
      if (topInstance.getLastReference() != null && 
         (topInstance.getLastRefName().endsWith(".class") || 
          topInstance.getLastRefName().startsWith("java.lang.System.") || 
          topInstance.getLastRefName().startsWith("java.lang.Runtime.") || 
          topInstance.getLastRefName().startsWith("java.lang.Integer.") || 
          topInstance.getLastRefName().startsWith("java.lang.Class."))) {
        newConditionList.remove(i--);
      }
    }
    
    return targetAssignFrom;
  }
  
  // since the SMT solver may give some very specific type to the instance which does
  // not make any sense (just a specific model), we only use this type information 
  // when 1) there are explicit type constraints for this instance in validateFormula 
  // or 2) its model value was not affected by previous model values
  private boolean shouldUseModelType(HashSet<Instance> instancesWithTypeTerm, Instance instance1, 
      Hashtable<String, List<Instance[]>> modelValueVarMap, String varValue) {
    
    boolean shouldUseModelType = false;
    if (instancesWithTypeTerm.contains(instance1)) {
      shouldUseModelType = true; // 1) there are explicit type constraints for this instance in validateFormula 
    }
    else {
      if (instancesWithTypeTerm.size() == 0 || 
         (instancesWithTypeTerm.size() == 1 && instancesWithTypeTerm.iterator().next().toString().equals("v9999"))) {
        shouldUseModelType = false; // there are only type constraints on the target instance, no need to use specific type
      }
      else if (modelValueVarMap.get(varValue).size() == 0 /* this solver value was not affected by previous solver values, thus has meanings */) {
        shouldUseModelType = true; // 2) its model value was not affected by previous model values
      }
    }
    return shouldUseModelType;
  }
  
  private void concretizeModelValue(Object[] toConcretize, String modelValue, Hashtable<String, List<Object[]>> toConcretizeList, 
      Hashtable<Instance, String> toConcretizeList2, Hashtable<String, List<Instance[]>> modelValueVarMap, 
      final Hashtable<Instance[], Integer> varIndexMap, Hashtable<Instance, String> instanceTypeMap, List<Condition> newConditionList, 
      List<BinaryConditionTerm> nonParamStaticTerms, HashSet<Object[]> concretized, HashSet<Object[]> concretizing) {
    
    // once we found nonParamTerms, cannot satisfy anyway
    if (nonParamStaticTerms.size() > 0) {
      return;
    }
    
    String fieldName     = (String) toConcretize[0];
    Instance lhsInstance = (Instance) toConcretize[1];
    Instance instance2   = (Instance) toConcretize[2];
    
    List<Instance[]> instances = modelValueVarMap.get(modelValue);
    if (instances == null) {
      // if cannot find in modelValueVarMap, it is likely to be a FreshInstanceOf term
      // e.g., FreshInstanceOf(Ljava/net/URL_2539627168683632).java.net.URL.getHost()Ljava/lang/String;_2539627171164395
      if (fieldName.contains(".")) {
        System.out.println("Model Value: " + modelValue + " not found for field name: " + fieldName + ", skip.");
      }
      else {
        nonParamStaticTerms.add((BinaryConditionTerm) toConcretize[3]);
      }
      return;
    }
    
//    // get the index of lhsInstance in satModel list
//    int indexInSatModel = Integer.MAX_VALUE;
//    Enumeration<Instance[]> keys = varIndexMap.keys();
//    while (keys.hasMoreElements()) {
//      Instance[] key = (Instance[]) keys.nextElement();
//      if (key[0] == lhsInstance) {
//        indexInSatModel = varIndexMap.get(key);
//        break;
//      }
//    }
//    
//    // sort the instances for concretizing, it seems that we should 
//    // always choose the one smaller and closest to the concretizing model term
//    final int indexInSatModel2 = indexInSatModel;
//    Collections.sort(instances, new java.util.Comparator<Instance[]>() {
//      @Override
//      public int compare(Instance[] o1, Instance[] o2) {
//        Integer index1 = varIndexMap.get(o1);
//        Integer index2 = varIndexMap.get(o2);
//        if (index1 == null || index2 == null) {
//          return 0;
//        }
//        int diff1 = indexInSatModel2 - index1;
//        int diff2 = indexInSatModel2 - index2;
//        return  (diff1 < 0) ? ((diff2 < 0) ? diff2 - diff1 : 1) : ((diff2 < 0) ? -1 : diff1 - diff2);
//      }
//    });
    
    if (fieldName.equals("@@array")) {
      String fieldType = "Unknown-Type";
      
      boolean hasConcretized = false;
      for (int i = 0; instances != null && i < instances.size() && !hasConcretized; i++) {
        Instance[] instancePair = instances.get(i);
        if (!instancePair[0].isBounded() || instancePair[0].getRight() != null) {
          if (instancePair[0].getLastReference() == null) { // itself has not be concretized
            String modelValue4Instance = toConcretizeList2.get(instancePair[0]);
            List<Object[]> parentToConcretizes = toConcretizeList.get(modelValue4Instance);
            Object[] parentToConcretize = null;
            for (Object[] parentToConcretize2 : parentToConcretizes) {
              if (parentToConcretize2[1] == instancePair[0]) {
                parentToConcretize = parentToConcretize2;
                break;
              }
            }
            if (!concretizing.contains(parentToConcretize) && // avoid endless recursions
                !concretized.contains(parentToConcretize) /* possible: ({Unbound} @ #!0) = 166429982658 where Unbound is Fresh instead of parameter */) { 
              concretizing.add(parentToConcretize);
              concretizeModelValue(parentToConcretize, modelValue4Instance, toConcretizeList, 
                  toConcretizeList2, modelValueVarMap, varIndexMap, instanceTypeMap, newConditionList, 
                  nonParamStaticTerms, concretized, concretizing);
              concretizing.remove(parentToConcretize);
            }
          }

          Reference lastRef = instancePair[0].getLastReference();
          if (lastRef != null || instancePair[0].getRight() != null) {
            if (lastRef != null && lastRef.getName().equals("v9999")) {
              continue;
            }
            Instance[] objs = null;
            
            String objType = lastRef != null ? lastRef.getType() : instancePair[0].getType();
            if (objType != null && objType.startsWith("[")) {
              objs = instancePair; // instance that assigned with this value
              fieldType = objType.substring(1); // skipping the initial [
              
              // concretize to this object
              try {
                // this is how we represent instance[index]
                lhsInstance.setValue(new Instance(objs[0], INSTANCE_OP.DUMMY, lhsInstance.getRight(), null));
              } catch (Exception e) {}
              
              String typeName = instanceTypeMap.get(lhsInstance);
              if (typeName != null) {
                // choose the more specify one
                if (Utils.isSubClass(fieldType, typeName)) {
                  fieldType = typeName;
                }
              }
              lhsInstance.setType(fieldType);

              // create instance2 and binary condition term
              BinaryConditionTerm term = createConditionRHS(lhsInstance, instance2, fieldType);
              newConditionList.add(new Condition(term));
              
              hasConcretized = true;
            }
          }
        }
      }
      
      if (!hasConcretized) {
        nonParamStaticTerms.add((BinaryConditionTerm) toConcretize[3]);
      }
    }
    else {
      String fieldType = "Unknown-Type";
      
      boolean hasConcretized = false;
      for (int i = 0; instances != null && i < instances.size() && !hasConcretized; i++) {
        Instance[] instancePair = instances.get(i);
        if (!instancePair[0].isBounded() || instancePair[0].getRight() != null) {
          if (instancePair[0].getLastReference() == null) { // itself has not be concretized
            String modelValue4Instance = toConcretizeList2.get(instancePair[0]);
            List<Object[]> parentToConcretizes = toConcretizeList.get(modelValue4Instance);
            Object[] parentToConcretize = null;
            for (Object[] parentToConcretize2 : parentToConcretizes) {
              if (parentToConcretize2[1] == instancePair[0]) {
                parentToConcretize = parentToConcretize2;
                break;
              }
            }
            if (!concretizing.contains(parentToConcretize) && // avoid endless recursions
                !concretized.contains(parentToConcretize) /* possible: ({Unbound} @ #!0) = 166429982658 where Unbound is Fresh instead of parameter */) { 
              concretizing.add(parentToConcretize);
              concretizeModelValue(parentToConcretize, modelValue4Instance, toConcretizeList, toConcretizeList2, modelValueVarMap, 
                  varIndexMap, instanceTypeMap, newConditionList, nonParamStaticTerms, concretized, concretizing);
              concretizing.remove(parentToConcretize);
            }
          }

          Reference lastRef = instancePair[0].getLastReference();
          if (lastRef != null || instancePair[0].getRight() != null) {
            if (lastRef != null && lastRef.getName().equals("v9999")) {
              continue;
            }
            Instance[] objs = null;

            String objType = lastRef != null ? lastRef.getType() : instancePair[0].getType();
            if (objType != null) {
              fieldType = WalaUtils.findFieldType(m_walaAnalyzer, objType, fieldName);
              fieldType = fieldType.equals("Unknown-Type") ? Requirements.pseudoImplTypes(objType, fieldName) : fieldType;
              if (!fieldType.equals("Unknown-Type")) {
                objs = instancePair; // instance that assigned with this value

                if (!objs[0].isOneOfDeclInstance(lhsInstance)) {
                  // concretize to this object
                  String typeName = instanceTypeMap.get(lhsInstance);
                  if (typeName != null) {
                    // choose the more specify one
                    if (Utils.isSubClass(fieldType, typeName)) {
                      fieldType = typeName;
                    }
                  }
                  objs[0].setField(fieldName, fieldType, "", lhsInstance, true, true); 
                  
                  // create instance2 and binary condition term
                  BinaryConditionTerm term = createConditionRHS(lhsInstance, instance2, fieldType);
                  newConditionList.add(new Condition(term));
                  
                  hasConcretized = true;
                }
              }
            }
          }
          else {
            // still failed to concretize due to bugs?
          }
        }
      }
      
      if (!hasConcretized) {
        //nonParamStaticTerms.add((BinaryConditionTerm) toConcretize[3]);
      }
    }
    
    concretized.add(toConcretize);
  }
  
  private BinaryConditionTerm createConditionRHS(Instance leftHandSide, Instance instance2, String typeName) {
    // create instance2
    Comparator comp = Comparator.OP_EQUAL;
    if (instance2.getValue().startsWith("#!")) {
      String fieldType = typeName;
      if (instance2.getValue().equals("#!21474836471")) {
        instance2 = new Instance("null", fieldType, null);
      }
      else if (!Utils.isPrimitiveType(fieldType)) { // e.g., #!2147483649 -> notnull
        instance2 = new Instance("null", fieldType, null);
        comp = Comparator.OP_INEQUAL;
      }
      else if (fieldType.equals("Z")) { // all non-0 booleans are casted to 1
        if (!instance2.getValueWithoutPrefix().equals("0")) {
          instance2 = new Instance("#!1", fieldType, null);
        }
      }
    }
    return new BinaryConditionTerm(leftHandSide, comp, instance2);
  }
  
  private Requirements splitModel(List<Condition> conditionList, boolean v1UsesInnerClass) {
    Hashtable<Instance, Requirement> requirementsMap = new Hashtable<Instance, Requirement>();
    
    for (Condition condition : conditionList) {
      BinaryConditionTerm term = (BinaryConditionTerm) condition.getConditionTerms().get(0);
      Instance topInstance = term.getInstance1().getToppestInstance();
      while (topInstance.getRight() != null) { // array access
        topInstance = topInstance.getLeft().getToppestInstance();
      }
      
      if (!topInstance.isConstant() && topInstance.getLastReference() != null) {
        String name = topInstance.getLastRefName();
        if (name.equals("v9999")) { // default name for target
          continue;
        }
        
        Requirement req = requirementsMap.get(topInstance);
        if (req == null) {
          req = new Requirement(topInstance.getLastRefName());
          requirementsMap.put(topInstance, req);
        }
        req.addRequirementTerm(term);
      }
    }
    
    Requirements requirements = new Requirements();
    Enumeration<Instance> keys = requirementsMap.keys();
    while (keys.hasMoreElements()) {
      Instance topInstance = (Instance) keys.nextElement();
      Requirement req = requirementsMap.get(topInstance);
      requirements.addRequirement(topInstance.getLastRefName(), req);
      boolean useInnerClass = topInstance.getLastRefName().equals("v1") && v1UsesInnerClass;
      
      // make topInstance v9999 (default name for target)
      Reference lastRef = topInstance.getLastReference();
      new Reference("v9999", lastRef.getType(), lastRef.getCallSites(), topInstance, null, true);
      req.setTargetInstance(topInstance, useInnerClass);
    }
    
    return requirements;
  }
  

  @SuppressWarnings("unchecked")
  private List<Condition> findMoreValuesAll(List<Condition> origSatModel, Summary origSummary, 
      Requirement origReq, int numOfSmaller, int numOfLargerEqual) {

    // get the original generated model values
    Object[] targets = findMoreValueTargets(origSatModel, origSummary);
    Hashtable<Instance, Instance> targetInstances     = (Hashtable<Instance, Instance>) targets[0];
    Hashtable<Instance, Condition> newSatModelMapping = (Hashtable<Instance, Condition>) targets[3];
    
    // find the original model values for target instances
    boolean allFieldReadFound = true;
    List<Instance> targetInstanceList   = new ArrayList<Instance>();
    List<Condition> origValueConditions = new ArrayList<Condition>();
    Hashtable<Instance, Instance> solverFormulaInstanceMap = new Hashtable<Instance, Instance>();
    Hashtable<Instance, Integer> origModelValueInts = new Hashtable<Instance, Integer>();
    Enumeration<Instance> keys = targetInstances.keys();
    while (keys.hasMoreElements() && allFieldReadFound) {
      Instance targetInstance = (Instance) keys.nextElement();
      Instance origModelValue = targetInstances.get(targetInstance);
      
      // get the original model value
      if (origModelValue != null && origModelValue.getValue().startsWith("#!")) {
        try {
          Integer origModelInt = Integer.parseInt(origModelValue.getValueWithoutPrefix());
          origModelValueInts.put(targetInstance, origModelInt);

          // create condition
          String fullName     = targetInstance.toString();
          String[] fieldNames = fullName.split("\\.");

          allFieldReadFound = false;
          if (fieldNames.length > 0) {
            String currentName = fieldNames[0]; // v1
            Reference reference = origSummary.getEffect().get(currentName);
            if (reference == null) { // e.g.: java.util.Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;_482682480861585.length
              allFieldReadFound = true;
              continue; // not related to parameters anyway
            }
            
            Instance fieldRead = findFieldRead(origSummary, targetInstance);
            if (fieldRead != null) {
              solverFormulaInstanceMap.put(targetInstance, fieldRead);
              targetInstanceList.add(targetInstance);
              // create condition
              BinaryConditionTerm term = new BinaryConditionTerm(
                  fieldRead, BinaryConditionTerm.Comparator.OP_EQUAL, origModelValue);
              origValueConditions.add(new Condition(term));
              allFieldReadFound = true;
            }
          }
        } catch (Exception e) {}
      }
    }

    if (targetInstanceList.size() > 0 && allFieldReadFound) {
      // create the basic formula that has the definitions
      origSummary.getPathConditions().addAll(origValueConditions);
      Object[] created = createValidatingFormula(origSummary, origReq);
      Formula validateFormula = (Formula) created[0];
      Hashtable<Instance, Instance> instanceMap = (Hashtable<Instance, Instance>) created[1];
      origSummary.getPathConditions().removeAll(origValueConditions);
      
      // find the conditions corresponding to the origValueConditions in validateFormula
      List<Condition> validateConditions = new ArrayList<Condition>();
      for (Condition condition : origValueConditions) {
        BinaryConditionTerm binaryTerm = (BinaryConditionTerm) condition.getConditionTerms().get(0);
        Instance instance1 = binaryTerm.getInstance1();
        Instance instance2 = binaryTerm.getInstance2();
        for (int i = validateFormula.getConditionList().size() - 1; i >= 0; i--) {
          Condition condition2 = validateFormula.getConditionList().get(i);
          if (condition2.getConditionTerms().size() == 1 && 
              condition2.getConditionTerms().get(0) instanceof BinaryConditionTerm) {
            BinaryConditionTerm binaryTerm2 = (BinaryConditionTerm) condition2.getConditionTerms().get(0);
            if (binaryTerm2.getComparator() == BinaryConditionTerm.Comparator.OP_EQUAL) {
              if (instanceMap.get(instance1) == binaryTerm2.getInstance1() && 
                  instance2.getValue().equals(binaryTerm2.getInstance2().getValue())) {
                validateConditions.add(condition2);
                break;
              }
            }
          }
        }
      }
      validateFormula.getConditionList().removeAll(validateConditions);

      // create and prepare the context
      int ctx = m_smtChecker.createContext();
      m_smtChecker.smtChecksInContext(ctx, validateFormula, null, true, false, false, true, false, false);
      
      // try all combinations
      List<List<Condition>> satisfiables = new ArrayList<List<Condition>>();
      findMoreValuesAllRec(ctx, satisfiables, null, targetInstanceList, validateConditions, 
          0, origModelValueInts, solverFormulaInstanceMap, numOfSmaller, numOfLargerEqual, true);
      
      // delete context
      m_smtChecker.deleteContext(ctx);
      
      // obtain the values that are satisfiable
      for (int i = 0, size = satisfiables.size(); i < size && i < 20 /* only take maximum of 20 */; i++) {
        List<Condition> satisfiable = satisfiables.get(i);
        
        Hashtable<Instance, Instance> newValuesMap = new Hashtable<Instance, Instance>();
        for (Condition condition : satisfiable) {
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) condition.getConditionTerms().get(0);
          Instance formulaInstance = binaryTerm.getInstance1();
          newValuesMap.put(formulaInstance, binaryTerm.getInstance2());
        }
        
        // append new values
        Enumeration<Instance> keys2 = solverFormulaInstanceMap.keys();
        while (keys2.hasMoreElements()) {
          Instance key2 = (Instance) keys2.nextElement();
          Instance formulaInstance = solverFormulaInstanceMap.get(key2);
          
          Condition condition = newSatModelMapping.get(key2);
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) condition.getConditionTerms().get(0);
          
          // append new value to the previous model values
          Instance prevModelValues = binaryTerm.getInstance2();
          String prevModelValuesStr = prevModelValues.getValue();
          
          String newModelValuesStr = prevModelValuesStr + "|";
          if (newValuesMap.get(formulaInstance) == null) {
            newModelValuesStr += prevModelValuesStr.substring(
                prevModelValuesStr.lastIndexOf("|") + 1, prevModelValuesStr.length());
          }
          else {
            newModelValuesStr += newValuesMap.get(formulaInstance).getValue();
          }
          
          // create a new condition for the new value
          BinaryConditionTerm term = new BinaryConditionTerm(binaryTerm.getInstance1(), binaryTerm.getComparator(), 
              new Instance(newModelValuesStr, "I", null));
          Condition newCondition = new Condition(term);
          newSatModelMapping.put(key2, newCondition);
        }
      }
      System.out.println(satisfiables.size() + " more values obtained." + 
          (satisfiables.size() > 20 ? " Only take the first 20." : ""));
      
//      // debug multi-values
//      for (List<Condition> satisfiable : satisfiables) {
//        for (Condition condition : satisfiable) {
//          System.out.print(condition.getConditionTerms().get(0).getInstances()[1].toString() + "|");
//        }
//        System.out.println();
//      }
    }

    // create the new SatModel
    List<Condition> newSatModel = new ArrayList<Condition>();
    for (Condition condition : origSatModel) {
      ConditionTerm term = condition.getConditionTerms().get(0);
      if (term instanceof BinaryConditionTerm) { // otherwise they are v1.field != null
        BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
        Condition newCondition = newSatModelMapping.get(binaryTerm.getInstance1());
        if (newCondition != null) {
          newSatModel.add(newCondition);
        }
        else {
          newSatModel.add(condition);
        }
      }
      else {
        newSatModel.add(condition);
      }
    }
    
    return newSatModel;
  }
  
  @SuppressWarnings("unchecked")
  private void findMoreValuesAllRec(int ctx, List<List<Condition>> satisiables, List<Condition> prevConditions, 
      List<Instance> targetInstances, List<Condition> validateConditions, int currIndex, 
      Hashtable<Instance, Integer> origModelValueInts, Hashtable<Instance, Instance> solverFormulaInstanceMap, 
      int numOfSmaller, int numOfLargerEqual, boolean equalOrig) {
    
    Instance targetInstance = targetInstances.get(currIndex);
    int origModelInt = origModelValueInts.get(targetInstance);
    Instance formulaInstance = solverFormulaInstanceMap.get(targetInstance);

    // try (orig - n1) ... (orig + n2)
    for (int i = 0; i < (numOfSmaller + numOfLargerEqual); i++) {
      // new value we want to check
      Instance newValue = null;
      if (i < numOfSmaller) {
        newValue = new Instance("#!" + (origModelInt - (numOfSmaller - i)), "I", null);
      }
      else {
        newValue = new Instance("#!" + (origModelInt + (i - numOfSmaller)), "I", null);
      }
      
      equalOrig &= (i == numOfSmaller);
      
      // create condition
      BinaryConditionTerm term = new BinaryConditionTerm(
          formulaInstance, BinaryConditionTerm.Comparator.OP_EQUAL, newValue);
      Condition condition = new Condition(term);
      
      // add to list
      List<Condition> currConditions = null;
      if (prevConditions == null) {
        currConditions = new ArrayList<Condition>();
      }
      else {
        currConditions = (List<Condition>) ((ArrayList<Condition>) prevConditions).clone();
      }
      currConditions.add(condition);
      
      // before go any further, check if the current conditions can be satisfy

      // create validateCtxConditions from currConditions
      List<List<Condition>> validateCtxConditions = new ArrayList<List<Condition>>();
      List<Condition> validateConditions2 = new ArrayList<Condition>();
      for (int j = 0, size = currConditions.size(); j < size; j++) {
        BinaryConditionTerm binaryTerm1 = (BinaryConditionTerm) currConditions.get(j).getConditionTerms().get(0);
        BinaryConditionTerm binaryTerm2 = (BinaryConditionTerm) validateConditions.get(j).getConditionTerms().get(0);
        
        validateConditions2.add(new Condition(new BinaryConditionTerm(
            binaryTerm2.getInstance1(), binaryTerm1.getComparator(), binaryTerm1.getInstance2())));
      }
      validateCtxConditions.add(validateConditions2);

      // check with SMT solver
      Object[] results = m_smtChecker.smtChecksInContext(
          ctx, null, validateCtxConditions, true, false, false, true, false, false);
      List<SMT_RESULT> smtCheckResults = (List<SMT_RESULT>) results[1];

      // good to continue
      if (smtCheckResults.get(0) == SMT_RESULT.SAT) {
        if (currIndex >= targetInstances.size() - 1) {
          if (!equalOrig) {
            satisiables.add(currConditions);
          }
        }
        else {
          findMoreValuesAllRec(ctx, satisiables, currConditions, targetInstances, validateConditions, 
              currIndex + 1, origModelValueInts, solverFormulaInstanceMap, numOfSmaller, numOfLargerEqual, equalOrig);
        }
      }
    }
  }
  
  // this method finds more values for each integer fields SEPERATELY
  @SuppressWarnings({ "unchecked", "unused" })
  private List<Condition> findMoreValuesSeperate(List<Condition> origSatModel, Summary origSummary, 
      Requirement origReq, int numOfSmaller, int numOfLarger) {

    // get the original generated model values
    Object[] targets = findMoreValueTargets(origSatModel, origSummary);
    Hashtable<Instance, Instance> targetInstances     = (Hashtable<Instance, Instance>) targets[0];
    Hashtable<String, Instance> targetInstanceNames   = (Hashtable<String, Instance>) targets[1];
    Hashtable<Instance, Instance> nonTargetInstances  = (Hashtable<Instance, Instance>) targets[2];
    Hashtable<Instance, Condition> newSatModelMapping = (Hashtable<Instance, Condition>) targets[3];
    
    // addition checks to obtain more model values
    Enumeration<Instance> keys = targetInstances.keys();
    while (keys.hasMoreElements()) {
      Instance targetInstance = (Instance) keys.nextElement();
      Instance origModelValue = targetInstances.get(targetInstance);
      
      // get the original model value
      Integer origModelInt = null;
      if (origModelValue != null && origModelValue.getValue().startsWith("#!")) {
        try {
          origModelInt = Integer.parseInt(origModelValue.getValueWithoutPrefix());
        } catch (Exception e) {}
      }
      if (origModelInt == null) {
        continue;
      }

      // try (orig - n1) ... (orig + n2)
      for (int i = 0; i < (numOfSmaller + numOfLarger); i++) {
        Hashtable<Instance, Instance> fixValues = (Hashtable<Instance, Instance>) nonTargetInstances.clone();
        
        // new value we want to check
        Instance newValue = null;
        if (i < numOfSmaller) {
          newValue = new Instance("#!" + (origModelInt - (numOfSmaller - i)), "I", null);
        }
        else {
          newValue = new Instance("#!" + (origModelInt + (i - numOfSmaller) + 1), "I", null);
        }
        fixValues.put(targetInstance, newValue); // add fix value

        // create the new summary for checking
        boolean allFixesPushed = true;
        List<Condition> pushedConditions = new ArrayList<Condition>();
        
        Enumeration<Instance> keys2 = fixValues.keys();
        while (keys2.hasMoreElements() && allFixesPushed) {
          Instance key2       = (Instance) keys2.nextElement();
          Instance value      = fixValues.get(key2);
          String fullName     = key2.toString();
          String[] fieldNames = fullName.split("\\.");

          allFixesPushed = false;
          if (fieldNames.length > 0) {
            String currentName = fieldNames[0]; // v1
            Reference reference = origSummary.getEffect().get(currentName);
            if (reference == null) { // e.g.: java.util.Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;_482682480861585.length
              allFixesPushed = true;
              continue; // not related to parameters anyway
            }
            
            Instance fieldRead = findFieldRead(origSummary, key2);
            if (fieldRead != null) {
              // add fix value as path condition
              BinaryConditionTerm term = new BinaryConditionTerm(
                  fieldRead, BinaryConditionTerm.Comparator.OP_EQUAL, value);
              Condition condition = new Condition(term);
              
              origSummary.getPathConditions().add(condition);
              pushedConditions.add(condition);
              allFixesPushed = true;
            }
          }
        }

        if (allFixesPushed) {
          // encode 1) summary path condition + 2) summary effect + 3) requirement conditions
          Object[] created = createValidatingFormula(origSummary, origReq);
          Formula validateFormula = (Formula) created[0];
          SMT_RESULT result = m_smtChecker.smtCheck(validateFormula, false, true, false, true, false, true);
          if (result.equals(SMT_RESULT.SAT)) {
            // parse satModel
            List<Condition> newConditionList = new ArrayList<Condition>();
            List<BinaryConditionTerm> nonParamTerms = new ArrayList<BinaryConditionTerm>();
            parseSatModel(m_smtChecker.getLastResult().getSatModel(), 
                newConditionList, nonParamTerms, false, validateFormula);

            // obtain the new model values for each instances
            Hashtable<Instance, Instance> newValuesMap = new Hashtable<Instance, Instance>();
            for (Condition condition : newConditionList) {
              ConditionTerm term = condition.getConditionTerms().get(0);
              if (term instanceof BinaryConditionTerm) {
                BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
                
                String instanceName = binaryTerm.getInstance1().toString();
                Instance instance = targetInstanceNames.get(instanceName);
                if (instance != null) {
                  newValuesMap.put(instance, binaryTerm.getInstance2());
                }
              }
            }

            // append new values
            Enumeration<Instance> keys3 = targetInstances.keys();
            while (keys3.hasMoreElements()) {
              Instance key3 = (Instance) keys3.nextElement();
              
              Condition condition = newSatModelMapping.get(key3);
              BinaryConditionTerm binaryTerm = (BinaryConditionTerm) condition.getConditionTerms().get(0);
              
              // append new value to the previous model values
              Instance prevModelValues = binaryTerm.getInstance2();
              String prevModelValuesStr = prevModelValues.getValue();
              
              String newModelValuesStr = prevModelValuesStr + "|";
              if (newValuesMap.get(key3) == null) {
                newModelValuesStr += prevModelValuesStr.substring(
                    prevModelValuesStr.lastIndexOf("|") + 1, prevModelValuesStr.length());
              }
              else {
                newModelValuesStr += newValuesMap.get(key3).getValue();
              }
              
              // create a new condition for the new value
              BinaryConditionTerm term = new BinaryConditionTerm(binaryTerm.getInstance1(), binaryTerm.getComparator(), 
                  new Instance(newModelValuesStr, "I", null));
              Condition newCondition = new Condition(term);
              newSatModelMapping.put(key3, newCondition);
            }
            
            System.out.println("More value: " + targetInstance + ": " + newValue);
          }
        }
        
        // remove the pushed conditions
        origSummary.getPathConditions().removeAll(pushedConditions);
      }
    }

    // create the new SatModel
    List<Condition> newSatModel = new ArrayList<Condition>();
    for (Condition condition : origSatModel) {
      ConditionTerm term = condition.getConditionTerms().get(0);
      if (term instanceof BinaryConditionTerm) { // otherwise they are v1.field != null
        BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
        Condition newCondition = newSatModelMapping.get(binaryTerm.getInstance1());
        if (newCondition != null) {
          newSatModel.add(newCondition);
        }
        else {
          newSatModel.add(condition);
        }
      }
      else {
        newSatModel.add(condition);
      }
    }
    
    return newSatModel;
  }

  private Instance findFieldRead(Summary origSummary, Instance instance) {
    Instance fieldRead = null;
    
    String fullName     = instance.toString();
    String[] fieldNames = fullName.split("\\.");
    String currentName  = fieldNames[0]; // v1
    
    Reference reference = origSummary.getEffect().get(currentName);
    if (reference != null) {
      fieldRead = reference.getInstance();
      for (int i = 1; i < fieldNames.length && fieldRead != null; i++) {
        reference = fieldRead.getField(fieldNames[i]);
  
        // if the summary does not have this field, create it
        if (reference == null) {
          int stepBack = fieldNames.length - i - 1;
          Instance instance2 = instance;
          for (int j = 0; j < stepBack; j++) {
            instance2 = instance2.getLastReference().getDeclaringInstance();
          }
          
          String type = instance2.getLastRefType();
          fieldRead.setField(fieldNames[i], type, "", new Instance("", null), true, true);
          reference = fieldRead.getField(fieldNames[i]);
        }
        
        currentName += "." + fieldNames[i];
        Instance nextFieldRead = null;
        for (Instance oldInstance : reference.getOldInstances()) {
          if (oldInstance.toString().equals(currentName)) {
            nextFieldRead = oldInstance;
            break;
          }
        }
        if (nextFieldRead == null) {
          if (reference.getInstance().toString().equals(currentName)) {
            nextFieldRead = reference.getInstance();
          }
        }
        fieldRead = nextFieldRead;
      }
    }
    return fieldRead;
  }
  
  private Object[] findMoreValueTargets(List<Condition> origSatModel, Summary origSummary) {
    Hashtable<Instance, Instance> targetInstances     = new Hashtable<Instance, Instance>();
    Hashtable<String, Instance> targetInstanceNames   = new Hashtable<String, Instance>();
    Hashtable<Instance, Instance> nonTargetInstances  = new Hashtable<Instance, Instance>();
    Hashtable<Instance, Condition> newSatModelMapping = new Hashtable<Instance, Condition>();

    // get the original generated model values
    for (Condition condition : origSatModel) {
      ConditionTerm term = condition.getConditionTerms().get(0);
      if (term instanceof BinaryConditionTerm) { // otherwise they are v1.field != null
        BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;

        if (binaryTerm.getComparator() == BinaryConditionTerm.Comparator.OP_EQUAL) {
          // put to fix value list or find more list
          Instance instance1 = binaryTerm.getInstance1();
          Reference lastRef = instance1.getLastReference();
          if (lastRef != null && lastRef.getType() != null && 
              lastRef.getType().equals("I") && lastRef.getDeclaringInstance() != null) {
            
            // do not get multiple values for __hashcode__
            if (lastRef.getName().equals("__hashcode__")) {
              continue;
            }
            
            targetInstances.put(instance1, binaryTerm.getInstance2());
            targetInstanceNames.put(instance1.toString(), instance1);
            newSatModelMapping.put(instance1, condition);
          }
          else {
            nonTargetInstances.put(instance1, binaryTerm.getInstance2());
          }
        }
      }
    }
    
    if (targetInstances.size() > 0) {
      // do not get more values for integer type instances that are used as array indices
      Relation relation = origSummary.getRelationMap().get("@@array");
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance indexInstance = relation.getDomainValues().get(i)[1];
        HashSet<Instance> involvedInstances = new HashSet<Instance>();
        findInvolvedIndexInstances(indexInstance, involvedInstances);
        for (Instance involvedInstance : involvedInstances) {
          Instance targetInstance = targetInstanceNames.get(involvedInstance.toString());
          if (targetInstance != null) {
            Instance value = targetInstances.get(targetInstance);
            targetInstances.remove(targetInstance);
            targetInstanceNames.remove(involvedInstance.toString());
            newSatModelMapping.remove(targetInstance);
            nonTargetInstances.put(targetInstance, value);
          }
        }
      }
    }
    
    return new Object[] {targetInstances, targetInstanceNames, nonTargetInstances, newSatModelMapping};
  }
  
  private void findInvolvedIndexInstances(Instance instance, HashSet<Instance> instances) {
    if (instances.contains(instance)) {
      return;
    }
    
    instances.add(instance);
    if (instance.isBounded() && !instance.isAtomic()) {
      findInvolvedIndexInstances(instance.getRight(), instances);
      findInvolvedIndexInstances(instance.getLeft(), instances);
    }
  }
  
  public SMTChecker getSMTChecker() {
    return m_smtChecker;
  }
  
  public static class DeductResult {
    
    private DeductResult(Requirements childReqs, Variable keyVariable, boolean returnValIsKey, boolean canEndByCtor) {
      this.childReqs      = childReqs;
      this.keyVariable    = keyVariable; // the key variable which will satisfy req after executing the target method
      this.returnValIsKey = returnValIsKey;
      this.canEndByCtor   = canEndByCtor;
    }
    
    public final Requirements childReqs;
    public final Variable     keyVariable;
    public final boolean      returnValIsKey;
    public final boolean      canEndByCtor;
  }
  
  private final IR              m_ir;
  private final SMTChecker      m_smtChecker;
  private final WalaAnalyzer    m_walaAnalyzer;
  private final int             m_moreValuesLower;
  private final int             m_moreValuesHigher;
  private final boolean         m_isFactoryOrCreateInner;
  private final ObjectGenerator m_objGenerator;
}
