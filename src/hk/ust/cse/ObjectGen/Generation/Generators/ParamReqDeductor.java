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
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.Solver.SolverLoader.SOLVER_RESULT;
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
  }
  
  // compute the necessary requirements on the parameters
  public DeductResult deductChildReqs(Summary summary, Requirement req) {
    Variable keyVariable   = null; // the key variable which will satisfy req after executing the target method
    boolean returnValIsKey = false;

    // encode 1) summary path condition + 2) summary effect + 3) requirement conditions
    Object[] created = createValidatingFormula(summary, req);
    Formula validateFormula = (Formula) created[0];
    SOLVER_RESULT result = m_smtChecker.smtCheck(validateFormula, false, true, false, true, true, true);
    if (!result.equals(SOLVER_RESULT.SAT)) {
      return null;
    }
    
    // parse satModel from (field @ 21474836472) to v1.field
    List<Condition> modelConditions = new ArrayList<Condition>();
    List<BinaryConditionTerm> nonParamTerms = new ArrayList<BinaryConditionTerm>();
    keyVariable = parseSatModel(m_smtChecker.getLastResult().getSatModel(), 
        modelConditions, nonParamTerms, req.getTargetInstance() != null, validateFormula);
    // target does not come from any of the parameters, so it 
    // should come from RET or static field or we do not need it
    if (keyVariable == null) {
      if (req.getTargetInstanceName().startsWith("L")) { // Lorg/apache/log4j/LogManager
        keyVariable = new Variable(req.getTargetInstanceName(), req.getTargetInstance().getLastRefType());
      }
      else if (!m_ir.getMethod().getReturnType().getName().toString().equals("V")) {
        keyVariable = new Variable(m_objGenerator.nextVariableName(), req.getTargetInstance().getLastRefType());
        returnValIsKey = true;
      }
    }
    
    // no way we can satisfy them because they are not parameters
    if (nonParamTerms.size() > 0) {
      return null;
    }

    Class<?> reqTargetType   = req.getTargetType();
    boolean v1UsesInnerClass = req.getUseInnerClass() || (!returnValIsKey && 
                               ((!m_ir.getMethod().isStatic() && m_ir.getMethod().isProtected()) || 
                               ((Modifier.isProtected(reqTargetType.getModifiers()) || 
                                 Modifier.isAbstract(reqTargetType.getModifiers())) && m_ir.getMethod().isInit())));
    
//    // ArrayList/Vector.elementData.length hack: Since solver only outputs one model, 
//    // thus limiting the elementData.length field to a particular value. However, in 
//    // reality, elementData.length can always be handled properly by ArrayList/Vector, 
//    // thus, we manual set the value to 10 so that the simple constructor can be used.
//    for (int i = 0, size = modelConditions.size(); i < size; i++) {
//      Condition condition = modelConditions.get(i);
//      if (condition.getConditionTerms().size() == 1) {
//        ConditionTerm term = condition.getConditionTerms().get(0);
//        if (term instanceof BinaryConditionTerm) {
//          BinaryConditionTerm newTerm = Requirements.elementDataLengthHack((BinaryConditionTerm) term);
//          if (newTerm != term) {
//            modelConditions.set(i, new Condition(newTerm));
//          }
//        }
//      }
//    }

    // only use concrete model values for inter-related variables
    Hashtable<Instance, Requirement> requirementsMap = 
        createDeductionConditions(summary, req, modelConditions, keyVariable, returnValIsKey);
    //Hashtable<Instance, Requirement> requirementsMap = splitModel(modelConditions); // the old complete split way
    Requirements childReqs = toDefaultTargetName(requirementsMap, v1UsesInnerClass);
    
    // if the method is <init>, make sure we have no more requirements for v1
    boolean canEndByCtor = false;
    if (m_ir.getMethod().isInit()) {
      Requirement v1Req = childReqs.getRequirement("v1");
      canEndByCtor = v1Req == null || m_objGenerator.onlyVarNotNullReq(v1Req, "v9999");
    }
    
    // the constructor will create v1
    if (canEndByCtor) {
      childReqs.removeRequirement("v1");
    }
    else if (m_ir.getMethod().isInit()) {
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
      List<ConditionTerm> terms = new ArrayList<ConditionTerm>();

      if (!summary.getMethodData().isStatic() && !m_isFactoryOrCreateInner) {
        // target == v1 or v2 or ...
        for (int i = 1; i <= summary.getMethodData().getParamList().size() && i <= 1 /* only allow target == v1 */; i++) {
          Reference reference = effect.get("v" + i);
          ConditionTerm term = new BinaryConditionTerm(
              req.getTargetInstance(), Comparator.OP_EQUAL, reference.getInstance());
          terms.add(term);
          
          if (i == 1) {
            reference.setType(req.getTargetInstance().getLastRefType()); // set to real type
          }
        }
      }
      else if (effect.containsKey("RET")) { // this invocation does not return void
        Reference reference = effect.get("RET");
        Instance retInstance = toRelationInstance(relationMap, readFieldMap, reference.getInstance(), readRelNameMap);
        terms.add(new BinaryConditionTerm(req.getTargetInstance(), Comparator.OP_EQUAL, retInstance));
        instanceMap.put(reference.getInstance(), retInstance);
      }
      if (terms.size() > 0) {
        conditionList.add(new Condition(terms));
      }
    }

    // add other requirement conditions from req (postcondition)
    int sizeBeforeReqConds = conditionList.size();
    Hashtable<Integer, List<ConditionTerm>> multiModelCombs = new Hashtable<Integer, List<ConditionTerm>>();
    for (Condition reqCond : req.getConditions()) {
      List<ConditionTerm> relTerms = new ArrayList<ConditionTerm>();
      for (ConditionTerm term : reqCond.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          Instance relInstance = toRelationInstance(relationMap, readFieldMap, instance, readRelNameMap);
          instanceMap.put(instance, relInstance);
        }
        if (term instanceof BinaryConditionTerm) {
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
          Instance relInstance1 = instanceMap.get(binaryTerm.getInstance1());
          Instance relInstance2 = instanceMap.get(binaryTerm.getInstance2());

          // contain multiple model values, e.g.: v1.size == #!1|#!2, v1.data.length == #!1|#!2
          if (relInstance2.isConstant() && relInstance2.getValue().startsWith("#!") && relInstance2.getValue().contains("|")) {
            splitMultiModelValues(multiModelCombs, relInstance1, binaryTerm.getComparator(), relInstance2);
          }
          else {
            relTerms.add(new BinaryConditionTerm(relInstance1, binaryTerm.getComparator(), relInstance2));
          }
        }
        else if (term instanceof TypeConditionTerm) {
          TypeConditionTerm typeTerm = (TypeConditionTerm) term;
          Instance relInstance1 = instanceMap.get(typeTerm.getInstance1());
          relTerms.add(new TypeConditionTerm(relInstance1, typeTerm.getComparator(), typeTerm.getTypeString()));
        }
      }
      conditionList.add(new Condition(relTerms));
      
      // add type condition term for field access and array elements
      BinaryConditionTerm binaryTerm = reqCond.getOnlyBinaryTerm();
      if (binaryTerm != null && binaryTerm.isNotEqualToNull()) {
        String type = null;
        if (binaryTerm.getInstance1().getLastReference() != null) { // field access
          type = binaryTerm.getInstance1().getLastRefType();
        }
        else if (binaryTerm.getInstance1().getRight() != null && 
                 binaryTerm.getInstance1().getType() != null) { // array access
          type = binaryTerm.getInstance1().getType();
        }

        // add type condition
        if (type != null) {
          Instance relInstance1 = instanceMap.get(binaryTerm.getInstance1());
          conditionList.add(new Condition(new TypeConditionTerm(
              relInstance1, TypeConditionTerm.Comparator.OP_INSTANCEOF, type)));
        }
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

    // add cast-ables not equal conditions (especially useful when one variable is a super class of another)
    HashSet<Instance> usedInstances = findUsedInstances(conditionList, sizeBeforeReqConds, relationMap);
    conditionList.addAll(createNotEqualConditions(usedInstances));
    
    // translate to Formula
    Formula formula = new Formula(conditionList, new AbstractMemory(refMap, null, relationMap));
    return new Object[] {formula, instanceMap};
  }

  // add cast-ables not equal conditions (especially useful when one variable is a super class of another)
  private List<Condition> createNotEqualConditions(HashSet<Instance> instances) {
    List<Condition> conditionList = new ArrayList<Condition>();
    
    // find the instances which need to add in-equal
    HashSet<Instance> objInstances = new HashSet<Instance>();
    for (Instance instance : instances) {
      findAddNotNullInstances(instance, objInstances);
    }
    List<Instance> instanceList = new ArrayList<Instance>(objInstances);
    
    Instance nullInstance = new Instance("null", "", null);
    for (int i = 0, size = instanceList.size(); i < size; i++) {
      Instance instance1 = instanceList.get(i);
      String type1 = instance1.getLastRefType();
      if (!Utils.isPrimitiveType(type1)) {
        for (int j = i + 1; j < size; j++) {
          Instance instance2 = instanceList.get(j);
          String type2 = instance2.getLastRefType();
          if (!Utils.isPrimitiveType(type2)) {
            if (!instance1.toString().equals(instance2.toString()) && 
                (Utils.canCastTo(type1, type2) || Utils.canCastTo(type2, type1))) {
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

    return conditionList;
  }
  
  private void findAddNotNullInstances(Instance instance, HashSet<Instance> objInstances) {
    if (!instance.isBounded()) {
      if (!instance.toString().equals("v9999")) {
        objInstances.add(instance);
      }
    }
    else if (!instance.isAtomic()) {
      findAddNotNullInstances(instance.getLeft(), objInstances);
      findAddNotNullInstances(instance.getRight(), objInstances);
    }
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
      String fieldName = instance.getLastReference().getReadRelName();
      if (fieldName != null) {
        readFieldNames.add(fieldName);

        Relation rel = relationMap.get(fieldName);
        int index = rel.getIndex(instance.getLastReference().getReadRelTime());
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
        String fieldType = reference.getType();
        String declType  = reference.getDeclaringInstance().getLastReference() != null ? 
            reference.getDeclaringInstance().getLastRefType() : reference.getDeclaringInstance().getType();
        
        // convert to array theory format
        Relation relation = relationMap.get(fieldName);
        if (relation == null) {
          relation = new Relation(fieldName, 1, true, new String[] {declType}, fieldType);
          relationMap.put(fieldName, relation);
        }
        else { // update relation type information
          if (!declType.equals(relation.getDomainTypes()[0])) {
            relation.setDomainTypes(new String[] {"not_null_reference"});
          }
          if (!fieldType.equals(relation.getRangeType())) {
            relation.setRangeType("Unknown-Type");
          }
        }
        
        // save the current instance before update
        String fullFieldName = reference.getLongName(); // v1.next
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
      relation = new Relation(relName, summaryRelation.getDomainDimension(), 
          summaryRelation.getDirection(), summaryRelation.getDomainTypes(), summaryRelation.getRangeType());
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
          String fieldType = nonRelationInstance.getLastReference().getType();
          String declType  = nonRelationInstance.getLastReference().getDeclaringInstance().getLastReference() != null ? 
              nonRelationInstance.getLastReference().getDeclaringInstance().getLastRefType() : 
              nonRelationInstance.getLastReference().getDeclaringInstance().getType();
          declType = declType != null ? declType : "not_null_reference";
          
          Relation relation = relationMap.get(fieldName);
          if (relation == null) {
            relation = new Relation(fieldName, 1, true, new String[] {declType}, fieldType);
            relationMap.put(fieldName, relation);
          }
          else { // update relation type information
            if (!declType.equals(relation.getDomainTypes()[0])) {
              relation.setDomainTypes(new String[] {"not_null_reference"});
            }
            if (!fieldType.equals(relation.getRangeType())) {
              relation.setRangeType("Unknown-Type");
            }
          }
          
          // perform relation.read(parentInstance)
          Instance parent = toRelationInstance(relationMap, readFieldMap, 
              nonRelationInstance.getLastReference().getDeclaringInstance(), readRelNameMap);
          
          Reference relationRef = relation.read(new Instance[] {parent}, nonRelationInstance.getLastRefType(), null);
          relationInstance = relationRef.getInstance();
          
          // handle fields for constant string
          if (parent.isStringConstant()) {
            if (fieldName.equals("count")) { // in case of #str.count, use the actual number
              relationInstance = new Instance("#!" + parent.getValueWithoutPrefix().length(), "I", null);
            }
            else if (fieldName.equals("offset")) { // in case of #str.offset, use 0
              relationInstance = new Instance("#!0", "I", null);
            }
          }
          
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
          relation = new Relation("@@array", 2, true, new String[] {"not_null_reference", "I"}, "Unknown-Type");
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

    String targetModelValue   = null;
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
        else if (term instanceof BinaryConditionTerm) {
          Instance instance1 = ((BinaryConditionTerm) term).getInstance1();
          if (instance1.getLastReference() != null && instance1.getLastRefName().startsWith(("__instanceof__"))) {
            instancesWithTypeTerm.add(instance1.getLastReference().getDeclaringInstance());
          }
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
        if (validateFormula.getRefMap().get("").get(lastRef.getName()) == null && 
           !lastRef.getName().equals("v9999") && 
           !lastRef.getName().endsWith(".class") && // give a wild card to .class
           !lastRef.getName().startsWith("java.lang.System.") &&  // give a wild card to java.lang.System.
           !lastRef.getName().startsWith("java.lang.Runtime.") && // give a wild card to java.lang.Runtime.
           !lastRef.getName().startsWith("java.lang.Integer.") && // give a wild card to java.lang.Integer.
           !lastRef.getName().startsWith("java.lang.Class.") && // give a wild card to java.lang.Class.
           !lastRef.getName().startsWith("com.sun.")) { // give a wild card to com.sun.
          // e.g.: java.util.Arrays.copyOf([Ljava/lang/Object;I)[Ljava/lang/Object;_482682480861585
          nonParamStaticTerms.add(binarySatModelTerm);
          continue;
        }
        
        // the "reference object" of a static field
        if (lastRef.getName().startsWith("L")) { // Lorg/apache/commons/collections/functors/ExceptionClosure
          continue;
        }
        
        String varValue = instance2.getValueWithoutPrefix(); // the model value from solver
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
            targetModelValue = varValue;
            if (instances.size() > 0) {
              String varName = instances.get(0)[0].getLastRefName();
              String varType = instances.get(0)[0].getLastRefType();
              targetAssignFrom = new Variable(varName, varType);
            }
          }
          else if (varValue.equals(targetModelValue)) {
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
          topInstance.getLastRefName().startsWith("java.lang.Class.") || 
          topInstance.getLastRefName().startsWith("com.sun."))) {
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
      if (fieldName.contains(".") || fieldName.equals("value") /* most likely ##str.value */ ) {
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
        // some of the method summaries might not have been merged cleanly, thus leaving some not 
        // merged fields like, java.... In reality, we can ignore most of them, but java.io should not
        if (fieldName.contains("java.io.")) {
          nonParamStaticTerms.add((BinaryConditionTerm) toConcretize[3]);
        }
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
  
  private Hashtable<Instance, Requirement> createDeductionConditions(Summary summary, Requirement req, 
      List<Condition> modelConditions, Variable keyVariable, boolean returnValIsKey) {
    
    List<Condition> deductConditions = new ArrayList<Condition>();

    // add path conditions to deductConditions
    Relation summaryArrayRel = summary.getRelationMap().get("@@array");
    HashSet<String> addedConditions = new HashSet<String>();
    HashSet<Instance> useConcreteValues = new HashSet<Instance>();
    Hashtable<Instance, Instance> readArrayMap = new Hashtable<Instance, Instance>();
    for (Condition condition : summary.getPathConditions()) {
      HashSet<Instance> topInstances = condition.getRelatedTopInstances(summary.getRelationMap());
      if (topInstances.size() > 1) { // correlated to multiple parameters
        // use concrete values for variables in multiple parameters conditions
        HashSet<Instance> instances = condition.getRelatedInstances(summary.getRelationMap(), false, false, true, false);
        useConcreteValues.addAll(instances); // should not have array read instances
      }
      else if (topInstances.size() > 0) {
        // e.g. java.lang.System.getProperty(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;_2039300846879621
        String topInstanceName = topInstances.iterator().next().toString();
        if (!topInstanceName.contains(".") || topInstanceName.startsWith("L")) {
          String conditionStr = condition.toString();
          if (!addedConditions.contains(conditionStr)) {
            addedConditions.add(condition.toString());
            
            // we want to use (v1.elementData @ #!0) format in the deductConditions
            if (conditionStr.contains("read_@@array_")) {
              HashSet<Instance> instances = condition.getRelatedInstances(summary.getRelationMap(), true, false, true, false);
              for (Instance instance : instances) {
                if (instance.isRelationRead() && !readArrayMap.containsKey(instance)) {
                  readArrayMap.put(instance, convertArrayRead1(instance, summaryArrayRel));
                }
              }
            }
            deductConditions.add(condition);
          }
        }
      }
    }
    addedConditions.clear();
    for (int i = 0, size = deductConditions.size(); i < size; i++) {
      Condition condition = deductConditions.get(i).replaceInstances(readArrayMap); // replace read_@@array_
      deductConditions.set(i, condition);
      addedConditions.add(condition.toString());
    }

    // create a model value mapping
    Hashtable<String, String> modelValues = new Hashtable<String, String>();
    for (Condition condition : modelConditions) {
      modelValues.put(condition.getOnlyBinaryTerm().getInstance1().toString(), 
                      condition.getOnlyBinaryTerm().getInstance2().toString());
    }
    
    // add req conditions to deductConditions
    Instance keyInstance = summary.getEffect().get(returnValIsKey ? "RET" : keyVariable.getVarName()).getInstance();
    for (Condition reqCond : req.getConditions()) {
      List<ConditionTerm> terms = new ArrayList<ConditionTerm>();
      for (ConditionTerm term : reqCond.getConditionTerms()) {
        if (term instanceof BinaryConditionTerm) {
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
          Instance instance1 = findCorrespond(binaryTerm.getInstance1(), keyInstance, summaryArrayRel, modelValues);
          Instance instance2 = findCorrespond(binaryTerm.getInstance2(), keyInstance, summaryArrayRel, modelValues);
          terms.add(new BinaryConditionTerm(instance1, binaryTerm.getComparator(), instance2));
        }
        else if (term instanceof TypeConditionTerm) {
          TypeConditionTerm typeTerm = (TypeConditionTerm) term;
          Instance instance1 = findCorrespond(typeTerm.getInstance1(), keyInstance, summaryArrayRel, modelValues);
          terms.add(new TypeConditionTerm(instance1, typeTerm.getComparator(), typeTerm.getTypeString()));
        }
      }
      Condition condition = new Condition(terms);
      HashSet<Instance> topInstances = condition.getRelatedTopInstances(summary.getRelationMap());
      if (topInstances.size() > 1) { // correlated to multiple parameters
        HashSet<Instance> instances = condition.getRelatedInstances(summary.getRelationMap(), false, true, true, false);
        useConcreteValues.addAll(instances);
      }
      else if (topInstances.size() > 0) {
        String conditionStr = condition.toString();
        if (!addedConditions.contains(conditionStr)) {
          deductConditions.add(condition);
          addedConditions.add(conditionStr);
        }
      }
    }
    
    // also use concrete values for v1.length, (v1 @ #!0) and (v1 @ (#!0 + #!1))
    for (int i = 0; i < deductConditions.size(); i++) {
      Condition condition = deductConditions.get(i);
      HashSet<Instance> instances = condition.getRelatedInstances(summary.getRelationMap(), false, true, true, true);
      
      for (Instance instance : instances) {
        // if it is an array length instance
        if (instance.hasDeclaringInstance()) {
          Instance declInstance = instance.getLastReference().getDeclaringInstance();
          if (instance.getLastRefName().equals("length") && declInstance.getLastReference() != null && 
              declInstance.getLastRefType().startsWith("[") && !declInstance.hasDeclaringInstance()) {
            useConcreteValues.add(instance);
          }
        }
        else if (instance.getLastReference() != null && instance.getLastRefType().startsWith("[") && 
                !instance.hasDeclaringInstance()) {
          useConcreteValues.add(instance);
        }
        else if (instance.getLeft() != null && instance.getLeft().getLastReference() != null && 
                 instance.getLeft().getLastRefType().startsWith("[") && 
                !instance.getLeft().hasDeclaringInstance()) { // (v1 @ #!0)
          useConcreteValues.add(instance);
        }
      }
    }
    
    // use concrete values for primitive and array parameters
    for (Condition condition : modelConditions) {
      Instance instance1 = condition.getOnlyBinaryTerm().getInstance1();
      if (!instance1.isBounded() && !instance1.hasDeclaringInstance() && !instance1.toString().equals("v9999")) { // v1
        String typeName = instance1.getLastRefType();
        
        // for parameter types, we still trust the concretization from parseSatModel
        instance1 = findCorrespond(instance1, 
            summary.getEffect().get(instance1.toString()).getInstance(), summaryArrayRel, modelValues);
        instance1.getLastReference().setType(typeName);
        
        // use concrete values for primitive and array parameters
        if (Utils.isPrimitiveType(typeName) || typeName.startsWith("[")) {
          useConcreteValues.add(instance1);
        }
      }
      else if (instance1.isBounded() && !instance1.isAtomic() && !instance1.getLeft().hasDeclaringInstance()) { // (v1 @ #!0)
        if (!instance1.getLeft().toString().equals("v9999")) {
          Instance found = findCorrespond(instance1, 
              summary.getEffect().get(instance1.getLeft().toString()).getInstance(), summaryArrayRel, modelValues);
          useConcreteValues.add(found);
        }
      }
    }
    
    if (useConcreteValues.size() > 0) {
      // construct a (summaryInstance - concrete) mapping
      // construct a (modelInstance - summaryInstance) mapping
      Hashtable<Instance, Instance> modelSummaryMap    = new Hashtable<Instance, Instance>();
      Hashtable<Instance, Instance> summaryConcreteMap = new Hashtable<Instance, Instance>();
      for (Instance useConcreteValue : useConcreteValues) {
        for (Condition modelCondition : modelConditions) {
          BinaryConditionTerm binaryTerm = modelCondition.getOnlyBinaryTerm();
          Instance instance1 = binaryTerm.getInstance1();
          Instance instance2 = binaryTerm.getInstance2();
          Instance topInstance = instance1.getToppestInstance();
          if (!topInstance.isBounded() && !topInstance.toString().equals("v9999")) { // v1
            if (instance1.toString().equals(useConcreteValue.toString())) {
              if (binaryTerm.isNotEqualToNull()) {
                // necessary because useConcreteValue may contain index instance to be concretized
                summaryConcreteMap.put(useConcreteValue, useConcreteValue);
              }
              else {
                summaryConcreteMap.put(useConcreteValue, instance2);
              }
              modelSummaryMap.put(instance1, useConcreteValue);
              break;
            }
          }
          else if (topInstance.isBounded() && !topInstance.isAtomic() && 
                   useConcreteValue.isBounded() && !useConcreteValue.isAtomic()) { // (v1 @ #!0)
            if (instance1.toString().equals(useConcreteValue.computeInnerArithmetic())) {
              if (binaryTerm.isNotEqualToNull()) {
                // necessary because useConcreteValue may contain index instance to be concretized
                summaryConcreteMap.put(useConcreteValue, useConcreteValue);
              }
              else {
                summaryConcreteMap.put(useConcreteValue, instance2);
              }
              modelSummaryMap.put(instance1, useConcreteValue);
              break;
            }
          }
        }
      }
      
      // replace occurrences of instances with concrete values
      addedConditions.clear();
      List<Condition> deductConditions2 = new ArrayList<Condition>();
      for (int i = 0, size = deductConditions.size(); i < size; i++) {
        Condition condition = deductConditions.get(i).replaceInstances(summaryConcreteMap);
        HashSet<Instance> topInstances = condition.getRelatedTopInstances(summary.getRelationMap());
        if (topInstances.size() > 0) {
          deductConditions2.add(condition);
          addedConditions.add(condition.toString());
        }
      }
      deductConditions = deductConditions2;
      
      // add model conditions for variables which use concrete values
      int addedModels = 0;
      HashSet<String> useConcreteValueStrs = new HashSet<String>();
      for (Instance instance : useConcreteValues) {
        instance = summaryConcreteMap.containsKey(instance) ? 
            instance : instance.replaceInstances(summaryConcreteMap) /* replace array index to concrete */;
        useConcreteValueStrs.add(instance.toString());
      }
      for (Condition condition : modelConditions) {
        HashSet<Instance> instances = condition.getRelatedInstances(new Hashtable<String, Relation>(), false, false, false, false);
        for (Instance instance : instances) {
          Instance topInstance = instance.getToppestInstance();
          if (!topInstance.toString().equals("v9999")) {
            if (useConcreteValueStrs.contains(instance.toString())) {
              condition = condition.replaceInstances(modelSummaryMap);
              String conditionStr = condition.toString();
              if (!addedConditions.contains(conditionStr)) {
                deductConditions.add(condition);
                addedConditions.add(condition.toString());
                addedModels++;
              }
              break;
            }
          }
        }
        if (addedModels >= useConcreteValues.size()) {
          break;
        }
      }
    }
    
    // ArrayList/Vector.elementData.length hack: Since solver only outputs one model, 
    // thus limiting the elementData.length field to a particular value. However, in 
    // reality, elementData.length can always be handled properly by ArrayList/Vector, 
    // thus, we manual set the value to 10 so that the simple constructor can be used.
    for (int i = 0, size = deductConditions.size(); i < size; i++) {
      BinaryConditionTerm term = deductConditions.get(i).getOnlyBinaryTerm();
      if (term != null) {
        BinaryConditionTerm newTerm = Requirements.elementDataLengthHack((BinaryConditionTerm) term);
        if (newTerm != term) {
          deductConditions.set(i, new Condition(newTerm));
        }
      }
    }
    // force to use the smallest size/elementCount value
    Requirements.listSizeRangeHack(deductConditions);
    
    // split model by parameter and form multiple requirements
    Hashtable<Instance, Requirement> reqsMap = splitModel(deductConditions);
    
    // for every parameter with only v1 != null in modelConditions, just use it
    Hashtable<Instance, Requirement> modelReqsMap = splitModel(modelConditions);
    Enumeration<Instance> keys = modelReqsMap.keys();
    while (keys.hasMoreElements()) {
      Instance topInstance = (Instance) keys.nextElement();
      Requirement modelReq = modelReqsMap.get(topInstance);

      // do not let v1.__hashcode__ == #!0 affect onlyVarNotNullReq
      BinaryConditionTerm hashCodeTerm = null;
      for (Condition condition : modelReq.getConditions()) {
        BinaryConditionTerm term = condition.getOnlyBinaryTerm();
        if (term.toString().contains(".__hashcode__ == #!")) {
          hashCodeTerm = term;
          modelReq.getConditions().remove(condition);
          break;
        }
      }
      
      String varName = topInstance.getLastRefName();
      Reference paramRef = summary.getEffect().get(varName);
      if (paramRef != null) {
        Instance paramInstance = paramRef.getInstance();
        if (reqsMap.get(paramInstance) != null) {
          boolean onlyNotNull = m_objGenerator.onlyVarNotNullReq(modelReq, varName);
          boolean onlyNull    = m_objGenerator.onlyVarNullReq(modelReq, varName);
          if (onlyNotNull || onlyNull) {
            // remove original
            reqsMap.remove(paramInstance);
            
            // add != null / == null
            paramRef.setType(topInstance.getLastRefType());
            Comparator comp = onlyNotNull ? Comparator.OP_INEQUAL : Comparator.OP_EQUAL;
            Condition condition = new Condition(new BinaryConditionTerm(
                paramInstance, comp, new Instance("null", paramRef.getType(), null)));
            Requirement newReq = new Requirement(varName);
            newReq.addCondition(condition);
            reqsMap.put(paramInstance, newReq);
            
            // also add __hashCond__ condition
            if (hashCodeTerm != null) {
              if (paramInstance.getField("__hashcode__") == null) {
                paramInstance.setField("__hashcode__", "I", "", new Instance("", null), true, true);
              }
              Instance hashCodeInstance = paramInstance.getField("__hashcode__").getInstance();
              newReq.addCondition(new Condition(new BinaryConditionTerm(
                  hashCodeInstance, hashCodeTerm.getComparator(), hashCodeTerm.getInstance2())));
            }
          }
        }
      }
    }
    
    return reqsMap;
  }

  // convert read_@@array_ to (v1.elementData @ #!0) format
  private Instance convertArrayRead1(Instance instance, Relation arrayRelation) {
    Instance converted = null;
    if (instance.isRelationRead()) {
      long readTime     = instance.getLastReference().getReadRelTime();
      int index         = arrayRelation.getIndex(readTime);
      Instance relObj   = arrayRelation.getDomainValues().get(index)[0];
      Instance relindex = arrayRelation.getDomainValues().get(index)[1];
      
      relObj   = convertArrayRead1(relObj, arrayRelation);
      relindex = convertArrayRead1(relindex, arrayRelation);
      converted = new Instance(relObj, INSTANCE_OP.DUMMY, relindex, null);
    }
    else if (instance.hasDeclaringInstance()) {
      Instance declInstance  = instance.getLastReference().getDeclaringInstance();
      Instance declInstance2 = convertArrayRead1(declInstance, arrayRelation);
      if (declInstance2 != declInstance) {
        Reference fieldRef1 = instance.getLastReference();
        Reference fieldRef2 = declInstance2.getField(fieldRef1.getName());
        if (fieldRef2 == null) {
          declInstance2.setField(fieldRef1.getName(), fieldRef1.getType(), "", new Instance("", null), true, true);
          fieldRef2 = declInstance2.getField(fieldRef1.getName());
        }
        converted = fieldRef2.getInstance();
      }
      else {
        converted = instance;
      }
    }
    else {
      converted = instance;
    }
    return converted;
  }

  // convert read_@@array_ to (v1.elementData @ #!0) format (will look through any previous updates)
  private Instance convertArrayRead2(Instance instance, Relation arrayRelation) {
    Instance converted = null;
    if (instance.isRelationRead()) {
      long readTime     = instance.getLastReference().getReadRelTime();
      int index         = arrayRelation.getIndex(readTime);
      Instance relObj   = arrayRelation.getDomainValues().get(index)[0];
      Instance relindex = arrayRelation.getDomainValues().get(index)[1];
      
      for (int i = index - 1; i >= 0; i--) {
        if (arrayRelation.isUpdate(i)) {
          if (arrayRelation.getDomainValues().get(i)[0] == relObj) {
            Instance indexInstance = arrayRelation.getDomainValues().get(i)[1];
            if (indexInstance.toString().equals(relindex.toString())) {
              converted = arrayRelation.getRangeValues().get(i);
              break;
            }
            else if (!indexInstance.isConstant() || !relindex.isConstant()) {
              // XXX this is not correct, because there could be many updates to left[indexInstance], 
              // and any one (or multiple or none) of them can equal to right. Will fix later
              converted = arrayRelation.getRangeValues().get(i);
              break;
            }
          }
        }
      }
      if (converted == null) {
        converted = new Instance(relObj, INSTANCE_OP.DUMMY, relindex, null);
      }
    }
    else {
      converted = instance;
    }
    return converted;
  }
  
  // find the corresponding field instance (with the same field path) from findFrom
  private Instance findCorrespond(Instance instance, Instance findFrom, Relation arrayRelation, Hashtable<String, String> modelValues) {
    Instance correspond = null;
    
    // in case find from is array_@@array_
    findFrom = convertArrayRead2(findFrom, arrayRelation);
    
    if (!instance.isBounded()) { // v9999.iteratorChain or (v9999.iteratorChain.elementData @ #!0).nextObjectSet
      String[] fieldNames = instance.getDeclFieldNames();
      if (fieldNames.length > 0) {
        Instance topInstance = instance.getToppestInstance();
        if (!topInstance.isBounded()) { // v9999
          Instance fieldInstance1   = findFrom; // v1
          Instance[] fieldInstances = instance.getDeclFieldInstances(); // v9999
          
          assert(fieldNames.length == fieldInstances.length);
          for (int i = 0; i < fieldNames.length; i++) {
            String fieldName     = fieldNames[i];
            Reference nextField1 = fieldInstance1.getField(fieldName);
            Reference nextField2 = fieldInstances[i].getLastReference();
            if (nextField1 == null) {
              fieldInstance1.setField(fieldName, nextField2.getType(), "", new Instance("", null), true, true); 
              nextField1 = fieldInstance1.getField(fieldName);
            }
            fieldInstance1 = nextField1.getInstance();
            fieldInstance1 = convertArrayRead2(fieldInstance1, arrayRelation);
          }
          correspond = fieldInstance1;
        }
        else { // (v9999.iteratorChain.elementData @ #!0)
          Instance topInstance2 = findCorrespond(topInstance, findFrom, arrayRelation, modelValues);
          if (topInstance2 != null) {
            // assign type
            if (topInstance.getType() != null) {
              if (topInstance2.getLastReference() != null) {
                topInstance2.getLastReference().setType(topInstance.getType());
              }
              else {
                topInstance2.setType(topInstance.getType());
              }
            }
            
            Instance fieldInstance1   = topInstance2; // v2
            Instance[] fieldInstances = instance.getDeclFieldInstances(); // (v9999.iteratorChain.elementData @ #!0)

            assert(fieldNames.length == fieldInstances.length);
            for (int i = 0; i < fieldNames.length; i++) {
              String fieldName     = fieldNames[i];
              Reference nextField1 = fieldInstance1.getField(fieldName);
              Reference nextField2 = fieldInstances[i].getLastReference();
              if (nextField1 == null) {
                fieldInstance1.setField(fieldName, nextField2.getType(), "", new Instance("", null), true, true); 
                nextField1 = fieldInstance1.getField(fieldName);
              }
              fieldInstance1 = nextField1.getInstance();
              fieldInstance1 = convertArrayRead2(fieldInstance1, arrayRelation);
            }
            correspond = fieldInstance1;
          }
        }
      }
      else {
        correspond = findFrom;
      }
    }
    else if (!instance.isAtomic()) { // (v9999.iteratorChain.elementData @ #!0)
      Instance left  = findCorrespond(instance.getLeft(), findFrom, arrayRelation, modelValues);
      Instance right = findCorrespond(instance.getRight(), findFrom, arrayRelation, modelValues);
      for (int i = arrayRelation.getFunctionCount() - 1; i >= 0; i--) {
        if (arrayRelation.isUpdate(i)) {
          if (arrayRelation.getDomainValues().get(i)[0] == left) {
            Instance indexInstance = arrayRelation.getDomainValues().get(i)[1];
            if (indexInstance.toString().equals(right.toString())) {
              correspond = arrayRelation.getRangeValues().get(i);
              break;
            }
            else {
              String indexValue = indexInstance.isConstant() ? indexInstance.toString() : indexInstance.computeArithmetic(modelValues);
              String rightValue = right.isConstant() ? right.toString() : right.computeArithmetic(modelValues);
              if (rightValue != null && rightValue.equals(indexValue)) {
                // XXX use the model value, this is not sound, but works in most common cases
                correspond = arrayRelation.getRangeValues().get(i);
                break;
              }
            }
          }
        }
      }
      if (correspond == null) {
        correspond = new Instance(left, instance.getOp(), right, null);
      }
      correspond = convertArrayRead2(correspond, arrayRelation);
    }
    else {
      correspond = instance;
    }
    
    return correspond;
  }
  
  private Hashtable<Instance, Requirement> splitModel(List<Condition> conditionList) {
    Hashtable<Instance, Requirement> requirementsMap = new Hashtable<Instance, Requirement>();
    for (Condition condition : conditionList) {
      HashSet<Instance> topInstances = condition.getRelatedTopInstances(new Hashtable<String, Relation>());
      for (Instance topInstance : topInstances) { /* should only have one */
        if (!topInstance.isConstant() && topInstance.getLastReference() != null) {
          if (topInstance.getLastRefName().equals("v9999")) { // default name for target
            continue;
          }
          
          Requirement req = requirementsMap.get(topInstance);
          if (req == null) {
            req = new Requirement(topInstance.getLastRefName());
            requirementsMap.put(topInstance, req);
          }
          req.addCondition(condition);
        }
      }
    }
    return requirementsMap;
  }
  
  private Requirements toDefaultTargetName(Hashtable<Instance, Requirement> requirementsMap, boolean v1UsesInnerClass) {
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
    
    public String toString() {
      return childReqs.toString();
    }
    
    public final Requirements childReqs;
    public final Variable     keyVariable;
    public final boolean      returnValIsKey;
    public final boolean      canEndByCtor;
  }
  
  private final IR              m_ir;
  private final SMTChecker      m_smtChecker;
  private final WalaAnalyzer    m_walaAnalyzer;
  private final boolean         m_isFactoryOrCreateInner;
  private final ObjectGenerator m_objGenerator;
}
