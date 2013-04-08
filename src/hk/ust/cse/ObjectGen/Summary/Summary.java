package hk.ust.cse.ObjectGen.Summary;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision.VirtualMachine.Relation;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.Wala.MethodMetaData;
import hk.ust.cse.Wala.WalaAnalyzer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Set;

import com.ibm.wala.ssa.IR;

public class Summary {
  
  public Summary(Formula formula, MethodMetaData methData) {
    this(formula.getConditionList(), formula.getRefMap().get(""), formula.getRelationMap(), methData);   
  }
  
  public Summary(List<Condition> pathCondition, Hashtable<String, Reference> methodRefs, 
      Hashtable<String, Relation> relationMap, MethodMetaData methData) {
    m_methData      = methData;
    m_pathCondition = new ArrayList<Condition>();
    m_effect        = new Hashtable<String, Reference>();
    m_relationMap   = new Hashtable<String, Relation>();
    
    initialize(pathCondition, methodRefs, relationMap);    
  }
  
  private void initialize(List<Condition> pathCondition, Hashtable<String, Reference> methodRefs, 
      Hashtable<String, Relation> relationMap) {
    // the path condition of the summary
    m_pathCondition.addAll(pathCondition);
    
    // the effect of the summary
    Enumeration<String> keys = methodRefs.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      m_effect.put(key, methodRefs.get(key));
    }
    
    // all relations, currently should only contains @@array
    keys = relationMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      m_relationMap.put(key, relationMap.get(key));
    }
  }
  
  // translate to the scope of the current summary
  public Instance translateScope(Instance instance, Hashtable<String, String> paramArgMap, 
      Hashtable<Instance, Instance> translatedMap, HashSet<List<Instance>> mergedInstances, 
      Hashtable<Instance, Instance> replaceMap, Long invokeTime) {

    if (paramArgMap == null) {
      return instance;
    }
    
    Instance translated = translatedMap.get(instance);
    if (translated == null) {
      if (!instance.isConstant()) {
        if (instance.isBounded()) {
          if (instance.isAtomic()) { // FreshInstanceOf
            translated = instance;
            // translate the fields
            mergeFieldEffect2(translated, instance, invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
          }
          else {
            translated = new Instance(instance.getInitCallSites(), instance.getCreateBlock());
            
            // since instance.getLeft() and instance.getRight() may be identical to instance, 
            // we need to add to translatedMap first
            translatedMap.put(instance, translated);
            
            Instance instance1 = translateScope(instance.getLeft(), paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
            Instance instance2 = translateScope(instance.getRight(), paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
            try {
              translated.setValue(new Instance(instance1, instance.getOp(), instance2, instance.getCreateBlock()));
            } catch (Exception e) {e.printStackTrace();}
          }
        }
        else { // v1, v1.field, invocation (but invocation strings should not exist as 
               // the callee summary should already been fully expanded)
          Instance topInstance   = instance;
          Instance translatedTop = null;
          Reference lastRef      = instance.getLastReference();
          
          HashSet<List<Object>> prevInstances = new HashSet<List<Object>>();
          while (translatedTop == null && !topInstance.isBounded() && 
                 topInstance.getLastReference().getDeclaringInstance() != null) {
            
            // avoid endless loop
            List<Object> current = new ArrayList<Object>();
            current.add(topInstance.getLastReference().getDeclaringInstance());
            current.add(topInstance.getLastReference());
            
            if (prevInstances.contains(current)) {
              break;
            }
            else {
              prevInstances.add(current);
              
              topInstance = topInstance.getLastReference().getDeclaringInstance();
              lastRef = topInstance.getLastReference();
              translatedTop = translatedMap.get(topInstance);
            }
          }
          
          // translate if not already translated
          if (translatedTop == null && lastRef != null) {
            // do not translate relation reads, they should be replaced 
            // all together when translating the relationMap
            if (lastRef.getName().startsWith("read_")) { // read relation
              translatedTop = topInstance;
            }
            else if (lastRef.getDeclaringInstance() == null && lastRef.getName().contains("(")) {
              // do not translate static invocations, e.g. 
              // java.lang.Thread.currentThread()Ljava/lang/Thread;_1684020070691140
              translatedTop = topInstance;
            }
            else if (lastRef.getDeclaringInstance() == null && lastRef.getName().endsWith(".class")) {
              // do not translate retrieve class, e.g., [Ljava/lang/Object.class
              translatedTop = topInstance;
            }
            else {
              // static fields e.g., Lorg/apache/log4j/spi/LoggingEvent.PARAM_ARRAY
              if (lastRef.getDeclaringInstance() == null && lastRef.getName().startsWith("L")) {
                translatedTop = topInstance;
              }
              else {
                String translatedName = paramArgMap.get(lastRef.getName());

                if (translatedName == null) {
                  System.out.println();
                }
                
                // get the corresponding reference
                Reference translatedRef = m_effect.get(translatedName);
                if (translatedRef == null) { // the translatedName could be a constant
                  // initially, just assume it is a constant and create the reference
                  translatedRef = new Reference(translatedName, null, "", new Instance("", null) /* dummy */, null, false);
                  // check it is really a constant
                  translatedRef = translatedRef.isConstantReference() ? translatedRef : null;
                }
                
                translatedTop = translatedRef.getInstance();
              }
              
              translatedMap.put(topInstance, translatedTop); // we are actually translating the toppest
              translatedMap.put(translatedTop, translatedTop); // translatedToppest should not be translated as well

              // since we have found out the match, merge them immediately
              if (translatedTop != topInstance) {
                mergeFieldEffect2(translatedTop, topInstance, invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
                replaceMap.put(topInstance, translatedTop);
              }
            }
          }
          else if (translatedTop == null && lastRef == null) {
            translatedTop = topInstance;
          }

          // instance's toppest should have been changed already (e.g., v1.field1 -> v6.field1), simply return it
          translated = (topInstance == instance) ? translatedTop : instance ;
        }
      }
      else {
        translated = instance;
      }
      translatedMap.put(instance, translated);      
    }
    
    return translated;
  }
  
  public boolean fullyExpanded(Reference invocation) {
    return findInvocationAsReturn(invocation) == null && 
           findInvocationAsEffect(invocation) == null;
  }
  
  // find any occurrences of this invocation's return value
  // note that, this will also include the instance from the callee's invocation
  // field, e.g., v1's "org.....getRightSubTree()Lorg/...;_1585092552168904" field
  public Collection<Instance> findInvocationAsReturn(Reference invocation) {
    Set<Instance> found   = new HashSet<Instance>();
    Set<Instance> visited = new HashSet<Instance>();
    
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      findInvocationAsReturn(m_effect.get(key).getInstance(), invocation, found, visited);
    }
    return found;
  }
  
  // find any occurrences of this invocation's return value for this instance
  private void findInvocationAsReturn(Instance instance, Reference invocation, 
      Collection<Instance> found, Collection<Instance> visited) {
    if (!visited.contains(instance)) {
      visited.add(instance);
      
      Reference lastRef = instance.getLastReference();
      if (lastRef != null && lastRef.getName().equals(invocation.getName())) {
        found.add(instance);
      }
      
      if (instance.isBounded() && !instance.isAtomic()) {
        findInvocationAsReturn(instance.getLeft(), invocation, found, visited);
        findInvocationAsReturn(instance.getRight(), invocation, found, visited);
      }
      
      for (Reference fieldRef : instance.getFields()) {
        findInvocationAsReturn(fieldRef.getInstance(), invocation, found, visited);
        for (Instance oldInstance : fieldRef.getOldInstances()) {
          findInvocationAsReturn(oldInstance, invocation, found, visited);
        }
      }
    }
  }
  
  public Collection<Instance> findInvocationAsEffect(Reference invocation) {
    Set<Instance> found   = new HashSet<Instance>();
    Set<Instance> visited = new HashSet<Instance>();
    
    // find in path condition
    for (Condition condition : m_pathCondition) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          findInvocationAsEffect(instance, invocation, found, visited);
        }
      }
    }
    
    // find in effect
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      findInvocationAsEffect(m_effect.get(key).getInstance(), invocation, found, visited);
    }
    
    // find in relationMap
    keys = m_relationMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Relation relation = m_relationMap.get(key);
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        for (Instance domainValue : domainValues) {
          findInvocationAsEffect(domainValue, invocation, found, visited);
        }
        Instance rangeValue = relation.getRangeValues().get(i);
        if (rangeValue != null) {
          findInvocationAsEffect(rangeValue, invocation, found, visited);
        }
      }
    }
    
    return found;
  }
  
  private void findInvocationAsEffect(Instance instance, Reference invocation, Collection<Instance> found, 
      Collection<Instance> visited) {
    if (!visited.contains(instance)) {
      visited.add(instance);
      
      for (Reference fieldRef : instance.getFields()) {
        if (fieldRef.getName().startsWith("_undecidable_" + invocation.getName())) {
          found.add(instance);
          break;
        }
      }
      
      if (instance.isBounded() && !instance.isAtomic()) {
        findInvocationAsEffect(instance.getLeft(), invocation, found, visited);
        findInvocationAsEffect(instance.getRight(), invocation, found, visited);
      }
      
      for (Reference fieldRef : instance.getFields()) {
        findInvocationAsEffect(fieldRef.getInstance(), invocation, found, visited);
        for (Instance oldInstance : fieldRef.getOldInstances()) {
          findInvocationAsEffect(oldInstance, invocation, found, visited);
        }
      }
    }
  }
  
  public Set<Reference> findRelationRead(String readStr) {
    Set<Reference> found  = new HashSet<Reference>();
    Set<Instance> visited = new HashSet<Instance>();
    
    // find in path condition
    for (Condition condition : m_pathCondition) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          findRelationRead(instance, readStr, found, visited);
        }
      }
    }
    
    // find in effect
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      findRelationRead(m_effect.get(key).getInstance(), readStr, found, visited);
    }
    
    // find in relationMap
    keys = m_relationMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Relation relation = m_relationMap.get(key);
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        for (Instance domainValue : domainValues) {
          findRelationRead(domainValue, readStr, found, visited);
        }
        Instance rangeValue = relation.getRangeValues().get(i);
        if (rangeValue != null) {
          findRelationRead(rangeValue, readStr, found, visited);
        }
      }
    }
    
    return found;
  }
  
  private void findRelationRead(Instance instance, String readStr, Collection<Reference> found, 
      Collection<Instance> visited) {
    
    if (!visited.contains(instance)) {
      visited.add(instance);
      
      if (!instance.isBounded() && instance.getLastRefName().equals(readStr)) {
        found.add(instance.getLastReference());
      }
      
      if (instance.isBounded() && !instance.isAtomic()) {
        findRelationRead(instance.getLeft(), readStr, found, visited);
        findRelationRead(instance.getRight(), readStr, found, visited);
      }
      
      for (Reference fieldRef : instance.getFields()) {
        findRelationRead(fieldRef.getInstance(), readStr, found, visited);
      }
    }
  }

  // instances: all instances containing hidden "_undecidable_" because of the invocation
  public void mergeFieldEffect(Instance instance, Reference invocation, Summary invocationSummary, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    
    // build argument-parameter mapping
    Hashtable<String, List<String>> argParamMap = new Hashtable<String, List<String>>();
    Enumeration<String> keys = paramArgMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      String arg = paramArgMap.get(key);
      List<String> paramList = argParamMap.get(arg);
      if (paramList == null) {
        paramList = new ArrayList<String>();
        argParamMap.put(arg, paramList);
      }
      paramList.add(key);
    }
    
    // merge instance
    String argName = instance.getToppestInstance().getLastRefName();
    List<String> paramNames = argParamMap.get(argName);

    // merge invocation to current
    for (String paramName : paramNames) {
      // XXX when there are multiple param for this argument, the invocation 
      // effects could overlap, so we need to consider the time of assignment!!!
      Reference invocationEffect = invocationSummary.getEffect().get(paramName);
      if (invocationEffect != null) {
        Instance invInstance = invocationEffect.getInstance();
        long invokeTime = Long.parseLong(invocation.getName().substring(invocation.getName().lastIndexOf('_') + 1));
        
        Instance translated = translateScope(invInstance, paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        if (instance != translated) {
          mergeFieldEffect2(instance, translated, invokeTime, null, translatedMap, mergedInstances, replaceMap);
          replaceMap.put(translated, instance);
        }
        replaceMap.put(invInstance, instance);
      }
    }
    
    // merge hidden to current, even though hiddenInstance is earlier than instance, 
    // hiddenInstance's fields may not always have been assigned earlier than instance's fields
    Reference hiddenEffect  = instance.getField("_undecidable_" + invocation.getName());
    Instance hiddenInstance = hiddenEffect.getInstance();
    mergeFieldEffect2(instance, hiddenInstance, null, null, translatedMap, mergedInstances, replaceMap);
    replaceMap.put(hiddenInstance, instance); // necessary otherwise there will be multiple v1
    
    // after merging field effects, instance contains all field effects
    // now need to set instance to what it is (constant) or where from (v6)
    hiddenEffect = instance.getField("_undecidable_" + invocation.getName()); // reference may have been overrided, re-get
    if (hiddenInstance.getLastReference() != hiddenEffect) {
      setInstanceOrigin(instance, hiddenInstance, hiddenEffect, hiddenInstance, replaceMap, null);
    }
  }
  
  public void mergeStaticFieldEffect(Summary invocationSummary, Long invokeTime, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    
    // the effect of the summary
    Enumeration<String> keys = invocationSummary.getEffect().keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      if (key.startsWith("L")) { // e.g., Lorg/apache/log4j/NDC
        Reference refFrom = invocationSummary.getEffect().get(key);
        Reference refTo   = m_effect.get(key);
        Instance instanceFrom = refFrom.getInstance();
        
        if (refTo != null) {
          mergeFieldEffect2(refTo.getInstance(), instanceFrom, 
              invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
        }
        else {
          Instance translated = translateScope(instanceFrom, 
              paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
          
          boolean setLastRef = instanceFrom.getLastReference() == refFrom;
          refTo = new Reference(refFrom.getName(), refFrom.getType(), refFrom.getCallSites(), translated, null, setLastRef);
          mergeFieldEffect2(refTo.getInstance(), instanceFrom, 
              invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
          m_effect.put(key, refTo);
        }
      }
    }
  }

  // the assign time to the instance fields are not decidable
  public void mergeFieldEffect2(Instance instanceTo, Instance instanceFrom, Long invokeTime, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    
    // avoid redundant merge
    List<Instance> instancePair = new ArrayList<Instance>();
    instancePair.add(instanceTo);
    instancePair.add(instanceFrom);
    if (mergedInstances.contains(instancePair)) {
      return;
    }
    else {
      mergedInstances.add(instancePair);
    }
    
    // merge each field
    for (Reference fieldRef : new ArrayList<Reference>(instanceFrom.getFields())) {
      // avoid copying v1_v1/v1_#!10 fields
      if (isv1_v1(fieldRef) && ((instanceTo.isBounded() || instanceFrom.isBounded()) || 
          ((!instanceTo.getLastRefName().equals(instanceFrom.getLastRefName()) || 
           (paramArgMap != null)) && instanceFrom.getLastRefName().contains("(")))) {
        continue;
      }

      Instance fieldInstance = fieldRef.getInstance();
      
      // merge to instanceTo
      Reference toField = instanceTo.getField(fieldRef.getName());
      if (toField == null || instanceFrom == instanceTo /* latter case should only for translating FreshInstance */) {
        Instance translated = translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        boolean lastRef = fieldInstance.getLastReference() == fieldRef;
        instanceTo.setField(fieldRef.getName(), fieldRef.getType(), fieldRef.getCallSites(), translated, lastRef, true);
        
        // set the life time for translated in fieldRefTo
        Reference fieldRefTo = instanceTo.getField(fieldRef.getName());
        setInstanceLifeTime(fieldRefTo, fieldRef, translated, fieldInstance, invokeTime);
        
        // only doing it to set life time for sub-field instances 
        if (!is_undecidable_(fieldRef)) {
          setInstanceLifeTime(fieldRefTo, translated, invokeTime, new HashSet<List<Object>>());
        }
        
        // also merge in the old instance list
        for (Instance oldInstance : new ArrayList<Instance>(fieldRef.getOldInstances())) {
          Instance translatedOld = translateScope(oldInstance, 
              paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
          
          fieldRefTo.getOldInstances().add(translatedOld);
          setInstanceLifeTime(fieldRefTo, fieldRef, translatedOld, oldInstance, invokeTime);
          
          // only doing it to set life time for sub-field instances 
          //setInstanceLifeTime(fieldRefTo, translatedOld, invokeTime, new HashSet<List<Object>>());
          
          if (oldInstance.getLastReference() == fieldRef) {
            translatedOld.setLastReference(fieldRefTo);
          }
          
          if (oldInstance != translatedOld) {
            replaceMap.put(oldInstance, translatedOld); // oldInstance could exist in path condition list
          }
        }  
      }
      else if (toField.getInstance().getLastReference() == toField) { // just a read field, merge together
        mergeReference1(instanceTo, fieldRef, toField, invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
      }
      else { // there is at least one assignment to the field
        mergeReference2(instanceTo, fieldRef, toField, invokeTime, paramArgMap, translatedMap, mergedInstances, replaceMap);
      }
    }
  }
  
  // assuming toRef().getLastReference() == toField
  private void mergeReference1(Instance instanceTo, Reference fromRef, Reference toRef, Long invokeTime, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    
    Instance fieldInstance = fromRef.getInstance();
    if (fieldInstance.getLastReference() == fromRef) { // just a read field also
      Instance translated = translateScope(fieldInstance, 
          paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
      
      // field Reference in instanceTo may have been changed, get the current one
      toRef = instanceTo.getField(toRef.getName());
      
      mergeFieldEffect2(toRef.getInstance(), translated, 
          invokeTime, null, translatedMap, mergedInstances, replaceMap);
      replaceMap.put(fieldInstance, toRef.getInstance()); // fieldInstance could exist in path condition list
      replaceMap.put(translated, toRef.getInstance()); // fieldInstance could exist in path condition list
    }
    else { // has been replaced
      if (isAssignedEarlier(toRef, fromRef, toRef.getInstance(), fieldInstance, invokeTime)) {
        Instance mergeFrom = null;
        for (Instance oldInstance : fromRef.getOldInstances()) {
          if (!isAssignedEarlier(toRef, fromRef, toRef.getInstance(), oldInstance, invokeTime)) {
            mergeFrom = oldInstance;
            break;
          }
        }
        
        if (mergeFrom != null) {
          Instance translated = translateScope(mergeFrom, 
              paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
          
          // field Reference in instanceTo may have been changed, get the current one
          toRef = instanceTo.getField(toRef.getName());
          
          mergeFieldEffect2(toRef.getInstance(), translated, 
              invokeTime, null, translatedMap, mergedInstances, replaceMap);
          replaceMap.put(mergeFrom, toRef.getInstance()); // mergeFrom could exist in path condition list
          replaceMap.put(translated, toRef.getInstance()); // mergeFrom could exist in path condition list
          
          if (mergeFrom.getLastReference() != fromRef) {
            // after merging field effects, mergeTo contains all field effects of mergeFrom, 
            // now need to set mergeTo to what it is (constant) or where from (v6)
            setInstanceOrigin(toRef.getInstance(), translated, fromRef, mergeFrom, replaceMap, invokeTime);
          }
        }
        
        toRef.putInstancesToOld();
        try {
          toRef.assignInstance(fieldInstance, false);
          setInstanceLifeTime(toRef, fromRef, fieldInstance, fieldInstance, invokeTime);
        } catch (Exception e) {e.printStackTrace();}
      }
      else {
        Instance translated = translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        // field Reference in instanceTo may have been changed, get the current one
        toRef = instanceTo.getField(toRef.getName());
        
        mergeFieldEffect2(toRef.getInstance(), translated, 
            invokeTime, null, translatedMap, mergedInstances, replaceMap);
        replaceMap.put(fieldInstance, toRef.getInstance()); // mergeFrom could exist in path condition list
        replaceMap.put(translated, toRef.getInstance()); // mergeFrom could exist in path condition list
        
        if (fieldInstance.getLastReference() != fromRef) {
          // after merging field effects, mergeTo contains all field effects of mergeFrom, 
          // now need to set mergeTo to what it is (constant) or where from (v6)
          setInstanceOrigin(toRef.getInstance(), translated, fromRef, fieldInstance, replaceMap, invokeTime);
        }
      }
      
      for (Instance oldInstance : fromRef.getOldInstances()) {
        Instance translatedOld = translateScope(oldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        toRef.getOldInstances().add(translatedOld);
        setInstanceLifeTime(toRef, fromRef, translatedOld, oldInstance, invokeTime);
        
        if (oldInstance.getLastReference() == fromRef) {
          translatedOld.setLastReference(toRef);
        }
        
        if (oldInstance != translatedOld) {
          replaceMap.put(oldInstance, translatedOld); // oldInstance could exist in path condition list
        }
      }
    }
  }

  // assuming toRef().getLastReference() != toField, i.e. there is at least one assignment already
  private void mergeReference2(Instance instanceTo, Reference fromRef, Reference toRef, Long invokeTime, 
      Hashtable<String, String> paramArgMap, Hashtable<Instance, Instance> translatedMap, 
      HashSet<List<Instance>> mergedInstances, Hashtable<Instance, Instance> replaceMap) {
    
    Instance fieldInstance = fromRef.getInstance();
    boolean isHelperRef    = is_undecidable_(fromRef) || isv1_v1(fromRef);
    if (fieldInstance.getLastReference() == fromRef /* just read */ || isHelperRef) {
      // decide which instance to merge to
      Instance mergeTo = null;
      if (isHelperRef) {
        mergeTo = toRef.getInstance();
      }
      else if (!isAssignedEarlier(toRef, fromRef, toRef.getInstance(), fieldInstance, invokeTime)) {
        for (Instance oldInstance : toRef.getOldInstances()) {
          if (isAssignedEarlier(toRef, fromRef, oldInstance, fieldInstance, invokeTime)) {
            mergeTo = oldInstance;
            break;
          }
        }
      }
      else {
        mergeTo = toRef.getInstance();
      }
      
      if (mergeTo == null) { // fieldInstance is the earliest
        Instance translated = translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        // field Reference in instanceTo may have been changed, get the current one
        toRef = instanceTo.getField(toRef.getName());
        toRef.getOldInstances().add(translated);
        setInstanceLifeTime(toRef, fromRef, translated, fieldInstance, invokeTime);
        
        if (fieldInstance.getLastReference() == fromRef) {
          translated.setLastReference(toRef);
        }
        
        if (fieldInstance != translated) {
          replaceMap.put(fieldInstance, translated); // oldInstance could exist in path condition list
        }
      }
      else {
        Instance translated = isHelperRef ? fieldInstance : translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        mergeFieldEffect2(mergeTo, translated, 
            invokeTime, null, translatedMap, mergedInstances, replaceMap);
        replaceMap.put(fieldInstance, mergeTo); // mergeFrom could exist in path condition list
        replaceMap.put(translated, mergeTo); // mergeFrom could exist in path condition list
      }
    }
    else {
      if (!isAssignedEarlier(toRef, fromRef, toRef.getInstance(), fieldInstance, invokeTime)) {
        Instance translated = translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        // field Reference in instanceTo may have been changed, get the current one
        toRef = instanceTo.getField(toRef.getName());
        toRef.getOldInstances().add(translated);
        setInstanceLifeTime(toRef, fromRef, translated, fieldInstance, invokeTime);
        
        if (fieldInstance != translated) {
          replaceMap.put(fieldInstance, translated); // oldInstance could exist in path condition list
        }

        // XXX may not always correct?
        if (!toRef.getOldInstances().contains(translated)) {
          List<Instance> oldInstances = new ArrayList<Instance>(toRef.getOldInstances());
          for (Instance oldInstance : oldInstances) {
            if (!isAssignedEarlier(toRef, fromRef, oldInstance, fieldInstance, invokeTime) && 
                oldInstance.getLastReference() == toRef) { // it is a read field
              mergeFieldEffect2(oldInstance, translated, 
                  invokeTime, null, translatedMap, mergedInstances, replaceMap);
              setInstanceOrigin(oldInstance, translated, fromRef, fieldInstance, replaceMap, invokeTime);
            }
          }
        }
      }
      else {
        Instance translated = translateScope(fieldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        // field Reference in instanceTo may have been changed, get the current one
        toRef = instanceTo.getField(toRef.getName());
        
        toRef.putInstancesToOld();
        try {
          toRef.assignInstance(translated, false);
          setInstanceLifeTime(toRef, fromRef, translated, fieldInstance, invokeTime);
        } catch (Exception e) {e.printStackTrace();}
      }
      
      // deal with the old list in fromRef 
      for (Instance oldInstance : new ArrayList<Instance>(fromRef.getOldInstances())) {
        Instance translatedOld = translateScope(oldInstance, 
            paramArgMap, translatedMap, mergedInstances, replaceMap, invokeTime);
        
        // field Reference in instanceTo may have been changed, get the current one
        toRef = instanceTo.getField(toRef.getName());
        
        toRef.getOldInstances().add(translatedOld);
        setInstanceLifeTime(toRef, fromRef, translatedOld, oldInstance, invokeTime);
        
        // XXX may not always correct?
        if (oldInstance.getLastReference() == fromRef) { // toRef's read becomes fromRef's latest before set
          if (!toRef.getOldInstances().contains(translatedOld)) {
            // try to find the latest override in toRef
            long latestSetTime = Long.MIN_VALUE;
            Instance latestSetInstance = null;
            for (Instance oldInstance2 : new ArrayList<Instance>(toRef.getOldInstances())) {
              if (isAssignedEarlier(toRef, fromRef, oldInstance2, oldInstance, invokeTime) && 
                  oldInstance2.getLastReference() != toRef && oldInstance2 != translatedOld) { // it is a set field
                if (toRef.getLifeTime(oldInstance2)[0] > latestSetTime) {
                  latestSetTime = toRef.getLifeTime(oldInstance2)[0];
                  latestSetInstance = oldInstance2;
                }
              }
            }
            
            if (latestSetInstance != null) { // found the latest set before this read
              setInstanceOrigin(translatedOld, latestSetInstance, toRef, latestSetInstance, replaceMap, invokeTime);
            }
            else { // no override set
              translatedOld.setLastReference(toRef);
            }
          }
        }
        else { // fromRef's earliest after read becomes toRef's set
          if (!toRef.getOldInstances().contains(translatedOld)) {
            for (Instance oldInstance2 : new ArrayList<Instance>(toRef.getOldInstances())) {
              if (!isAssignedEarlier(toRef, fromRef, oldInstance2, oldInstance, invokeTime) && 
                  oldInstance2.getLastReference() == toRef && oldInstance2 != translatedOld) { // it is a read field
                setInstanceOrigin(oldInstance2, translatedOld, fromRef, oldInstance, replaceMap, invokeTime);
              }
            }
          }
        }
        
        if (oldInstance != translatedOld) {
          replaceMap.put(oldInstance, translatedOld); // oldInstance could exist in path condition list
        }
      }
    }
  }

  private static void setInstanceLifeTime(Reference refTo, Reference refOri, Instance instanceTo, Instance instanceOri, Long invokeTime) {
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

  private static void setInstanceLifeTime(Reference ref, Instance instance, Long invokeTime, HashSet<List<Object>> setted) {
    List<Object> toSet = new ArrayList<Object>();
    toSet.add(ref);
    toSet.add(instance);
    if (setted.contains(toSet)) {
      return;
    }
    
    if (invokeTime != null) {      
      ref.resetInstanceLiftTime(instance, invokeTime, Long.MAX_VALUE /* not useful in Summary */);
      setted.add(toSet);
      
      // merge each field
      for (Reference fieldRef : instance.getFields()) {
        // avoid copying v1_v1/v1_#!10 fields
        if (isv1_v1(fieldRef)) {
          continue;
        }

        // only doing it to set life time for sub-field instances 
        if (!is_undecidable_(fieldRef)) {
          setInstanceLifeTime(fieldRef, fieldRef.getInstance(), invokeTime, setted);
        }
        
        // also the old instance list
        for (Instance oldInstance : fieldRef.getOldInstances()) {
          setInstanceLifeTime(fieldRef, oldInstance, invokeTime, setted);
        }
      }
    }
  }
  
  private boolean isAssignedEarlier(Reference ref1, Reference ref2, Instance instance1, Instance instance2, Long invokeTime) {
    Long[] time1 = ref1.getLifeTime(instance1);
    Long[] time2 = ref2.getLifeTime(instance2);
    
    if (time1 != null) {
      if (invokeTime != null) {
        return time1[0] < invokeTime;
      }
      else if (time2 != null) {
        return time1[0] < time2[0];
      }
      else {
        return false;
      }
    }
    else {
      return false;
    }
  }
  
  public void setInstanceOrigin(Instance instanceToSet, Instance translatedOrigin, Reference refWithOrigin, 
      Instance instanceOrigin, Hashtable<Instance, Instance> replaceMap, Long invokeTime) {

    if (instanceOrigin.getLastReference() != refWithOrigin) { // v1.field contains instance v6 or #!0
      if (translatedOrigin.isBounded()) {
        if (!instanceToSet.isBounded()) {
          try {
            instanceToSet.setValue(translatedOrigin);
          } catch (Exception e) {e.printStackTrace();}
        }
      }
      else { // refWithOrigin is previously assigned with instanceOrigin
        Reference lastRef = translatedOrigin.getLastReference();
        if (lastRef.getInstance() == translatedOrigin) { // has not been replaced
          lastRef.getInstances().clear();
          try {
            lastRef.assignInstance(instanceToSet, true);
            setInstanceLifeTime(lastRef, lastRef, instanceToSet, translatedOrigin, invokeTime);
          } catch (Exception e) {e.printStackTrace();}
        }
        else {
          lastRef.getOldInstances().remove(translatedOrigin);
          lastRef.getOldInstances().add(instanceToSet);
          instanceToSet.setLastReference(lastRef);
          setInstanceLifeTime(lastRef, lastRef, instanceToSet, translatedOrigin, invokeTime);
        }
        replaceMap.put(translatedOrigin, instanceToSet);
      }
    }
  }
  
  // find all invocation references of this summary
  public Collection<Reference> findAllInvocations() {
    Set<Reference> found = new HashSet<Reference>();
    Set<Instance> visted = new HashSet<Instance>();
    
    // find in path condition
    for (Condition condition : m_pathCondition) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          findAllInvocations(instance, found, visted);
        }
      }
    }
    
    // find in effect
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      findAllInvocations(m_effect.get(key).getInstance(), found, visted);
    }
    return found;
  }

  // find all invocation references of this summary for this instance
  private void findAllInvocations(Instance instance, Collection<Reference> found, Collection<Instance> visited) {
    if (!visited.contains(instance)) {
      visited.add(instance);
      
      Reference lastRef = instance.getLastReference();
      if (lastRef != null && lastRef.getName().contains("_") && 
          lastRef.getName().contains(".") && !is_undecidable_(lastRef)) {
        try {
          Long.parseLong(lastRef.getName().substring(lastRef.getName().lastIndexOf("_") + 1));
          found.add(lastRef);
        } catch (Exception e) {/* not invocation */}
      }
      
      if (instance.isBounded() && !instance.isAtomic()) {
        findAllInvocations(instance.getLeft(), found, visited);
        findAllInvocations(instance.getRight(), found, visited);
      }

      for (Reference fieldRef : instance.getFields()) {
        findAllInvocations(fieldRef.getInstance(), found, visited);
      }
    }
  }
  
  public Hashtable<String, Reference> getEffect() {
    return m_effect;
  }
  
  public Hashtable<String, Relation> getRelationMap() {
    return m_relationMap;
  }
  
  public MethodMetaData getMethodData() {
    return m_methData;
  }
  
  public List<Condition> getPathConditions() {
    return m_pathCondition;
  }
  
  // generate persistent string of this summary
  public String toPersistentString() {    
    StringBuilder str = new StringBuilder();
    Hashtable<Instance, Integer> instanceNumMap   = new Hashtable<Instance, Integer>();
    Hashtable<Reference, Integer> referenceNumMap = new Hashtable<Reference, Integer>();
    
    // collect all references and instances and assign each with a number
    findAllInstancesReferences(referenceNumMap, instanceNumMap);
    
    // all instances
    Enumeration<Instance> instances = instanceNumMap.keys();
    while (instances.hasMoreElements()) {
      Instance instance = (Instance) instances.nextElement();
      int num1  = instance.getLeft() == null ? -1 : instanceNumMap.get(instance.getLeft());
      int num2  = instance.getRight() == null ? -1 : instanceNumMap.get(instance.getRight());
      int numOp = instance.getOp() == null ? -1 : instance.getOp().toIndex();
      str.append(instanceNumMap.get(instance)).append("\n");
      str.append(num1).append(" ").append(numOp).append(" ").append(num2).append("\n");
      str.append(instance.getValue() == null ? " " : instance.getValue().replace("\n", "@n")).append("\n");
      str.append(instance.getType() == null ? " " : instance.getType()).append("\n");
      
      int num3 = instance.getLastReference() == null ? -1 : referenceNumMap.get(instance.getLastReference());
      str.append(num3).append("\n");
      Hashtable<String, Reference> fields = instance.getFieldSet();
      Enumeration<String> fieldNames = fields.keys();
      while (fieldNames.hasMoreElements()) {
        String fieldName = (String) fieldNames.nextElement();
        str.append(fieldName.replace("\n", "@n")).append(" ")
           .append(referenceNumMap.get(fields.get(fieldName))).append("\n");
      }
      str.append("\n");
    }
    str.append("\n");
    
    // all references
    Enumeration<Reference> references = referenceNumMap.keys();
    while (references.hasMoreElements()) {
      Reference reference = (Reference) references.nextElement();
      str.append(referenceNumMap.get(reference)).append("\n");
      str.append(reference.getType() == null ? " " : reference.getType()).append("\n");
      str.append(reference.getName() == null ? " " : reference.getName().replace("\n", "@n")).append("\n");
      
      for (Instance instance : reference.getInstances()) {
        str.append(instanceNumMap.get(instance)).append("\n");
        Long[] lifeTime = reference.getLifeTime(instance);
        str.append(lifeTime == null ? " " : lifeTime[0]).append("\n");
      }
      str.append("\n");
      for (Instance instance : reference.getOldInstances()) {
        str.append(instanceNumMap.get(instance)).append("\n");
        Long[] lifeTime = reference.getLifeTime(instance);
        str.append(lifeTime == null ? " " : lifeTime[0]).append("\n");
      }
      str.append("\n");
      int num = reference.getDeclaringInstance() == null ? -1 : instanceNumMap.get(reference.getDeclaringInstance());
      str.append(num).append("\n\n");
    }
    str.append("\n");
    
    // m_pathCondition
    for (Condition condition : m_pathCondition) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        if (term instanceof BinaryConditionTerm) {
          BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
          Integer num1 = instanceNumMap.get(binaryTerm.getInstance1());
          Integer num2 = instanceNumMap.get(binaryTerm.getInstance2());
          str.append("b ").append(num1).append(" ")
             .append(binaryTerm.getComparator().toIndex()).append(" ").append(num2);
        }
        else if (term instanceof TypeConditionTerm) {
          TypeConditionTerm typeTerm = (TypeConditionTerm) term;
          Integer num1 = instanceNumMap.get(typeTerm.getInstance1());
          str.append("t ").append(num1).append(" ")
             .append(typeTerm.getComparator().toIndex()).append(" ").append(typeTerm.getTypeString());
        }
        str.append("|"); // separate each conditionTerm
      }
      str.append("\n");
    }
    str.append("\n");
    
    // m_effect
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Integer num = referenceNumMap.get(m_effect.get(key));
      str.append(key).append(" ").append(num).append("\n");
    }
    str.append("\n");
    
    // m_relationMap
    keys = m_relationMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Relation relation = m_relationMap.get(key);
      str.append(relation.getName()).append("\n");
      str.append(relation.getDomainDimension()).append("\n");
      str.append(relation.getDirection()).append("\n");
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        for (Instance domainValue : domainValues) {
          Integer num = instanceNumMap.get(domainValue);
          str.append(num).append("|");
        }
        str.append("\n");
        Instance rangeValue = relation.getRangeValues().get(i);
        str.append(rangeValue == null ? "" : instanceNumMap.get(rangeValue)).append("\n");
        str.append(relation.getFunctionTimes().get(i)).append("\n");
      }
      str.append("\n");
    }
    str.append("\n");
    
    // m_methData
    str.append(m_methData.getMethodSignature());
    
    return str.toString();
  }
  
  private void findAllInstancesReferences(Hashtable<Reference, Integer> references, Hashtable<Instance, Integer> instances) {
    HashSet<Object> visited = new HashSet<Object>();
    
    // m_pathCondition
    for (Condition condition : m_pathCondition) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          findAllInstancesReferences(instance, references, instances, visited);
        }
      }
    }
    
    // m_effect
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      findAllInstancesReferences(m_effect.get(keys.nextElement()), references, instances, visited);
    }
    
    // m_relationMap
    keys = m_relationMap.keys();
    while (keys.hasMoreElements()) {
      Relation relation = m_relationMap.get(keys.nextElement());
      for (int i = 0, size = relation.getFunctionCount(); i < size; i++) {
        Instance[] domainValues = relation.getDomainValues().get(i);
        for (Instance domainValue : domainValues) {
          findAllInstancesReferences(domainValue, references, instances, visited);
        }
        Instance rangeValue = relation.getRangeValues().get(i);
        findAllInstancesReferences(rangeValue, references, instances, visited);
      }
    }
  }
  
  private void findAllInstancesReferences(Instance instance, Hashtable<Reference, Integer> references, 
      Hashtable<Instance, Integer> instances, HashSet<Object> visited) {
    if (instance == null || visited.contains(instance)) {
      return;
    }
    
    visited.add(instance);
    instances.put(instance, instances.size());
    
    findAllInstancesReferences(instance.getLeft(), references, instances, visited);
    findAllInstancesReferences(instance.getRight(), references, instances, visited);
    findAllInstancesReferences(instance.getLastReference(), references, instances, visited);
    for (Reference reference : instance.getFields()) {
      findAllInstancesReferences(reference, references, instances, visited);
    }
  }
  
  private void findAllInstancesReferences(Reference reference, Hashtable<Reference, Integer> references, 
      Hashtable<Instance, Integer> instances, HashSet<Object> visited) {
    if (reference == null || visited.contains(reference)) {
      return;
    }
    
    visited.add(reference);
    references.put(reference, references.size());
    
    for (Instance instance : reference.getInstances()) {
      findAllInstancesReferences(instance, references, instances, visited);
    }
    for (Instance instance : reference.getOldInstances()) {
      findAllInstancesReferences(instance, references, instances, visited);
    }
    findAllInstancesReferences(reference.getDeclaringInstance(), references, instances, visited);
  }
  
  // create summary from persistent string
  public static Summary fromPersistentString(String persistentString, WalaAnalyzer walaAnalyzer) {
    String[] lines = persistentString.split("\n");
    
    Hashtable<Integer, Instance> instanceNumMap   = new Hashtable<Integer, Instance>();
    Hashtable<Integer, Reference> referenceNumMap = new Hashtable<Integer, Reference>();
    
    // read all instances
    int current = 0;
    for (; current < lines.length && lines[current].length() > 0; current++) {
      int num = Integer.parseInt(lines[current++]);
      
      // left and right instances
      String[] leftRight = lines[current++].split(" ");
      int numLeft  = Integer.parseInt(leftRight[0]);
      int numOp    = Integer.parseInt(leftRight[1]);
      int numRight = Integer.parseInt(leftRight[2]);
      
      // value and type
      String value = lines[current++].replace("@n", "\\n");
      String type  = lines[current++];
      value = value.equals(" ") ? null : value;
      type = type.equals(" ") ? null : type;
      
      // last reference
      int numLastRef = Integer.parseInt(lines[current++]);
      
      // fields
      Hashtable<String, Integer> fieldSet = new Hashtable<String, Integer>();
      while (lines[current].length() > 0) {
        int index = lines[current].lastIndexOf(' ');
        String fieldName   = lines[current].substring(0, index).replace("@n", "\\n");
        String instanceNum = lines[current].substring(index + 1);
        fieldSet.put(fieldName, Integer.valueOf(instanceNum));
        current++;
      }
      
      // re-create the instance
      Instance instance = Instance.createInstance(
          num, numLeft, numOp, numRight, value, type, numLastRef, fieldSet, instanceNumMap, referenceNumMap);
      instanceNumMap.put(num, instance);
    }
    current++;

    // read all references
    for (; current < lines.length && lines[current].length() > 0; current++) {   
      int num = Integer.parseInt(lines[current++]); 
      
      // type and name
      String type = lines[current++];
      String name = lines[current++].replace("@n", "\\n");
      type = type.equals(" ") ? null : type;
      name = name.equals(" ") ? null : name;
      
      // instance list and old instance list
      Hashtable<Integer, Long[]> lifeTimes = new Hashtable<Integer, Long[]>(); 
      List<Integer> instances    = new ArrayList<Integer>();
      List<Integer> oldInstances = new ArrayList<Integer>();
      while (lines[current].length() > 0) {
        int instanceNum = Integer.parseInt(lines[current++]);
        instances.add(instanceNum);

        String startTime = lines[current++];
        if (!startTime.equals(" ")) {
          lifeTimes.put(instanceNum, new Long[] {Long.parseLong(startTime), Long.MAX_VALUE});
        }
      }
      current++;
      while (lines[current].length() > 0) {
        int oldInstanceNum = Integer.parseInt(lines[current++]);
        oldInstances.add(oldInstanceNum);
        
        String startTime = lines[current++];
        if (!startTime.equals(" ")) {
          lifeTimes.put(oldInstanceNum, new Long[] {Long.parseLong(startTime), Long.MAX_VALUE});
        }
      }
      current++;
      
      // declaring instance
      int declInstanceNum = Integer.parseInt(lines[current++]);
      
      Reference reference = Reference.createReference(num, type, name, instances, 
          oldInstances, lifeTimes, declInstanceNum, instanceNumMap, referenceNumMap);
      referenceNumMap.put(num, reference);
    }
    current++;
    
    // re-create m_pathCondition
    List<Condition> pathCondition = new ArrayList<Condition>();
    for (; current < lines.length && lines[current].length() > 0; current++) {
      List<ConditionTerm> terms = new ArrayList<ConditionTerm>();
      
      String[] termStrs = lines[current].split("\\|");
      for (String termStr : termStrs) {
        ConditionTerm term = null;
        String[] termStrList = termStr.split(" ");
        if (termStrList[0].equals("b")) {
          int num1 = Integer.parseInt(termStrList[1]);
          int num2 = Integer.parseInt(termStrList[3]);
          Instance instance1 = num1 < 0 ? null : instanceNumMap.get(num1);
          Instance instance2 = num2 < 0 ? null : instanceNumMap.get(num2);
          BinaryConditionTerm.Comparator op = 
            BinaryConditionTerm.Comparator.fromIndex(Integer.parseInt(termStrList[2]));
          term = new BinaryConditionTerm(instance1, op, instance2);
        }
        else if (termStrList[0].equals("t")) {
          int num1 = Integer.parseInt(termStrList[1]);
          String typeString = termStrList[3];
          Instance instance1 = num1 < 0 ? null : instanceNumMap.get(num1);
          TypeConditionTerm.Comparator op = 
            TypeConditionTerm.Comparator.fromIndex(Integer.parseInt(termStrList[2]));
          term = new TypeConditionTerm(instance1, op, typeString);
        }
        terms.add(term);
      }
      pathCondition.add(new Condition(terms));
    }
    current++;
    
    // re-create m_effect
    Hashtable<String, Reference> effect = new Hashtable<String, Reference>();
    for (; current < lines.length && lines[current].length() > 0; current++) {
      String[] referenceStrs = lines[current].split(" ");
      int num = Integer.parseInt(referenceStrs[1]);
      Reference reference = num < 0 ? null : referenceNumMap.get(num);
      effect.put(referenceStrs[0], reference);
    }
    current++;

    // re-create m_relationMap
    Hashtable<String, Relation> relationMap = new Hashtable<String, Relation>();
    for (; current < lines.length && lines[current].length() > 0; current++) {
      // create relation
      String relName = lines[current++];
      int domainDim  = Integer.parseInt(lines[current++]);
      boolean direction = Boolean.parseBoolean(lines[current++]);
      Relation relation = new Relation(relName, domainDim, direction, new String[] {"not_null_reference", "I"}, "Unknown-Type");
      
      List<Instance[]> domainValuesList = relation.getDomainValues();
      List<Instance>   rangeValueList   = relation.getRangeValues();
      List<Long>       funcTimeList     = relation.getFunctionTimes();
      for (; current < lines.length && lines[current].length() > 0; current++) {
        // domain value instances
        Instance[] domainValues = new Instance[domainDim];
        String[] domainValuesStr = lines[current++].split("\\|");
        for (int i = 0; i < domainValuesStr.length; i++) {
          int num = Integer.parseInt(domainValuesStr[i]);
          Instance instance = num < 0 ? null : instanceNumMap.get(num);
          domainValues[i] = instance;
        }
        domainValuesList.add(domainValues);
        
        // range value instance
        Instance rangeValue = null;
        String rangeValueStr = lines[current++];
        if (rangeValueStr.length() > 0) {
          int num = Integer.parseInt(rangeValueStr);
          rangeValue = num < 0 ? null : instanceNumMap.get(num);
        }
        rangeValueList.add(rangeValue);

        // function time
        long funcTime = Long.parseLong(lines[current]);
        funcTimeList.add(funcTime);
      }
      relationMap.put(relName, relation);
    }
    current++;
    
    // re-create m_methData
    String methodSig = lines[current];
    IR ir = Jar2IR.getIR(walaAnalyzer, methodSig);
    MethodMetaData methData = new MethodMetaData(ir);
    
    // re-create the summary
    return new Summary(pathCondition, effect, relationMap, methData);
  }
  
  public Summary deepClone() {
    return deepClone(new Hashtable<Object, Object>());
  }
  
  @SuppressWarnings("unchecked")
  public Summary deepClone(Hashtable<Object, Object> cloneMap) {
    // deep clone path condition
    List<Condition> clonePathCondition = new ArrayList<Condition>();
    for (Condition condition : m_pathCondition) {
      clonePathCondition.add(condition.deepClone(cloneMap));
    }

    // deep clone effect
    Hashtable<String, Reference> cloneEffect = (Hashtable<String, Reference>) m_effect.clone();
    Enumeration<String> keys = cloneEffect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      cloneEffect.put(key, m_effect.get(key).deepClone(cloneMap));
    }
    
    // deep clone relation Map
    Hashtable<String, Relation> cloneRelationMap = (Hashtable<String, Relation>) m_relationMap.clone();
    keys = cloneRelationMap.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      cloneRelationMap.put(key, m_relationMap.get(key).deepClone(cloneMap));
    }
    
    return new Summary(clonePathCondition, cloneEffect, cloneRelationMap, m_methData);
  }
  
  public String toString() {
    StringBuilder str = new StringBuilder();
    str.append(m_methData.getName() + ": \n");
    
    str.append("Path Conditions: \n");
    List<String> conditionStrings = new ArrayList<String>();
    for (Condition condition : m_pathCondition) {
      if (!isFreshNotNullTerm(condition)) {
        String conditionString = condition.toString();
        if (!conditionStrings.contains(conditionString)) {
          conditionStrings.add(conditionString);
        }
      }
    }
    for (String conditionString : conditionStrings) {
      str.append(conditionString).append("\n");
    }

    // collect parameters including "this"
    List<String> toOutputs = new ArrayList<String>();
    for (int i = 1; i <= m_methData.getParamList().size(); i++) {
      toOutputs.add("v" + i);
    }
    
    // collect static fields
    Enumeration<String> keys = m_effect.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      if (key.startsWith("L")) {
        toOutputs.add(key);
      }
    }
    
    // output
    str.append("\nEffect: \n");
    HashSet<Instance> visited = new HashSet<Instance>();
    for (int i = 0; i < toOutputs.size(); i++) {
      Hashtable<String, Set<Instance>> overrided = new Hashtable<String, Set<Instance>>();
      Reference reference = m_effect.get(toOutputs.get(i));
      str.append(toOutputs.get(i)).append(": \n");
      str.append((reference != null) ? 
          toStringWithFields(reference.getInstance(), toOutputs.get(i), overrided, visited) : "no effect").append("\n");
      
      // output the overrided branches' effect
      while (overrided.size() > 0) {
        Hashtable<String, Set<Instance>> overrided2 = new Hashtable<String, Set<Instance>>();
        keys = overrided.keys();
        while (keys.hasMoreElements()) {
          String key = (String) keys.nextElement();
          str.append(key).append(": \n");
          for (Instance instance : overrided.get(key)) {
            if (!instance.isConstant()) {
              str.append(toStringWithFields(instance, key, overrided2, visited)).append("\n"); // could find new overrides
            }
          }
        }
        overrided = overrided2;        
      }
    }
    
    // return
    Hashtable<String, Set<Instance>> overrided = new Hashtable<String, Set<Instance>>();
    Reference reference = m_effect.get("RET");
    str.append("RET: ").append((reference != null) ? 
        toStringWithFields(reference.getInstance(), "RET", overrided, visited): "no return").append("\n");
    
    return str.toString();
  }
  
  private String toStringWithFields(Instance instance, String prefix, 
      Hashtable<String, Set<Instance>> overrided, HashSet<Instance> visited) {
    StringBuilder ret = new StringBuilder();
    
    String instanceStr = instance.toString();
    if (!prefix.equals(instanceStr)) { // do not show read instance (because read has no effect)
      ret.append(prefix).append(": ").append(instanceStr).append("\n");
    }
    
    if (!visited.contains(instance)) {
      visited.add(instance);
      
      // effect for each field of this instance
      for (Reference field : instance.getFields()) {
        String fieldName = field.getName();
        if (instance.getLastReference() != null && instance.getLastRefName().contains("(") && 
            fieldName.contains("_v")) { // this invocation has no return summary, thus effect not merged
          continue;
        }
        
        if (!fieldName.contains("(")) { // do not show invocations
          ret.append(toStringWithFields(field.getInstance(), prefix + "." + field.getName(), overrided, visited));
        }
        
        // override instances are saved in oldInstances list, we 
        // should also show the effects on these override instances
        Set<Instance> overridedInstances = field.getOldInstances();
        if (overridedInstances.size() > 0) {
          String fullFieldName = prefix + "." + fieldName;
          Set<Instance> instances = overrided.get(fullFieldName);
          if (instances == null) {
            instances = new HashSet<Instance>();
            overrided.put(fullFieldName, instances);
          }
          instances.add(overridedInstances.iterator().next()); //XXX why random one?
        }
      }
    }
    return ret.toString();
  }
  
  private boolean isFreshNotNullTerm(Condition condition) {
    boolean freshNotNullTerm = false;
    
    if (condition.getConditionTerms().size() == 1) {
      ConditionTerm term = condition.getConditionTerms().get(0);
      if (term instanceof BinaryConditionTerm) {
        BinaryConditionTerm binaryTerm = (BinaryConditionTerm) term;
        if (binaryTerm.getComparator() == Comparator.OP_INEQUAL && 
            "null".equals(binaryTerm.getInstance2().getValue())) {
          Instance instance1 = binaryTerm.getInstance1();
          if (instance1.getValue() != null && instance1.getValue().startsWith("FreshInstanceOf")) {
            freshNotNullTerm = true;
          }
        }
      }
    }
    return freshNotNullTerm;
  }
  
  private static boolean is_undecidable_(Reference ref) {
    return ref.getName().startsWith("_undecidable_");
  }
  
  private static boolean isv1_v1(Reference ref) {
    return ref.getName().matches("v[0-9]+_(?:null|[v#][\\S]+)");
  }
  
  private final List<Condition>              m_pathCondition;
  private final Hashtable<String, Reference> m_effect;
  private final Hashtable<String, Relation>  m_relationMap;
  private final MethodMetaData               m_methData;
}
