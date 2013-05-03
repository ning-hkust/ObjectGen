package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Requirements;
import hk.ust.cse.ObjectGen.Generation.TestCase.AssignmentStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

public class AssignFieldGenerator extends AbstractGenerator {

  public AssignFieldGenerator(Generator allTypeGenerator, int accessibility) {
    super(allTypeGenerator, accessibility);
  }

  // assuming that, all fields in req are accessible, currently only support static fields
  @Override
  @SuppressWarnings("unchecked")
  public Sequence generate(Requirement req, List<Requirement> ancestorReqs) {
    Sequence genSequence = null;
    
    // check if requirement can be set directly
    genSequence = trySetDirectly(req);
    
    // if not, generate this array object
    if (genSequence == null) {
      Hashtable<Instance, Requirement> requirementsMap = new Hashtable<Instance, Requirement>();
      Hashtable<String, Instance> fieldInstanceMap     = new Hashtable<String, Instance>();
      Requirements childReqs                           = new Requirements();
      
      String targetTypeName = null;
      Class<?> targetType   = null;
      for (int i = 0, size = req.getConditions().size(); i < size && childReqs != null; i++) {
        BinaryConditionTerm binaryTerm = req.getCondition(i).getOnlyBinaryTerm();
        if (binaryTerm == null) {
          continue;
        }
        
        Instance instance1 = binaryTerm.getInstance1();
        Instance instance2 = binaryTerm.getInstance2();
        if (!instance1.isBounded() && instance1.getLastReference().getDeclaringInstance() == null) { // v1 != null
          // currently, we don't support modifying non-static fields
        }
        else { // Lorg/apache/log4j/NDC.ht != null, v1.field != null
          Instance topInstance = instance1.getToppestInstance();
          if (!topInstance.isBounded() && topInstance.getLastRefName().startsWith("L")) { // Lorg/apache/log4j/NDC
            targetTypeName = topInstance.getLastRefName();
            targetType = Utils.findClass(targetTypeName);
            
            // find the first level field name
            String fieldName         = null;
            Instance fieldInstance   = null;
            Instance currentInstance = instance1;
            while (currentInstance.getLastReference().getDeclaringInstance() != null) {
              fieldName       = currentInstance.getLastRefName();
              fieldInstance   = currentInstance;
              currentInstance = currentInstance.getLastReference().getDeclaringInstance();
            }
            
            Field targetField = Utils.getInheritedField(targetType, fieldName);
            if (targetField != null && 
                Modifier.isPublic(targetField.getModifiers()) && !Modifier.isFinal(targetField.getModifiers())) {
              
              Instance instance = fieldInstanceMap.get(fieldName);
              if (instance == null) {
                instance = new Instance("", null);
                fieldInstanceMap.put(fieldName, instance);
                
                // make instance v9999 (default name for target)
                Reference lastRef = fieldInstance.getLastReference();
                new Reference("v9999", lastRef.getType(), lastRef.getCallSites(), instance, null, true);
                for (Reference fieldRef : fieldInstance.getFields()) {
                  instance.setField(fieldRef.getName(), fieldRef.getType(), 
                      fieldRef.getCallSites(), fieldRef.getInstances(), true, true);
                }
              }
              
              Requirement childReq = requirementsMap.get(instance);
              if (childReq == null) {
                childReq = new Requirement(fieldName);
                childReq.setTargetInstance(instance, false);
                requirementsMap.put(instance, childReq);
                childReqs.addRequirement(fieldName, childReq);
              }
              
              // fieldInstance has been changed to instance
              if (instance1 == fieldInstance) {
                binaryTerm = new BinaryConditionTerm(instance, binaryTerm.getComparator(), instance2);
              }
              childReq.addCondition(new Condition(binaryTerm));
            }
            else {
              // currently, we only support modifying public non-final field
              childReqs = null;
            }
          }
          else {
            // currently, we only support modifying static field
            childReqs = null;
          }
        }
      }

      // generate the necessary child sequences and assign to fields
      targetType = Utils.findClass(targetTypeName);
      if (childReqs != null && targetType != null) {
        if ((m_accessibility == 0 && Modifier.isPublic(targetType.getModifiers())) || 
            (m_accessibility == 1 && !Modifier.isPrivate(targetType.getModifiers()))) { 
          if (req.getTargetInstance().getLastRefName().startsWith("L")) { // Lorg/apache/log4j/NDC
            // generate recursively for the child requirements
            Hashtable<Long, String> prevHashCodeVarMap = 
                (Hashtable<Long, String>) m_allTypeGenerator.getHashCodeVarMap().clone();
            GenerationResult genResult = m_allTypeGenerator.gen4ChildReqs(childReqs, ancestorReqs);
            
            if (!genResult.hasNotSat()) {
              // create genSequence
              String className     = req.getTargetInstance().getLastRefName();
              String classJavaName = Utils.getClassTypeJavaStr(className);
              
              Variable assignTo = new Variable(classJavaName, className);
              genSequence = new Sequence(assignTo);
              
              // create assignment statements, assigned the key variable of each sequence to field
              for (String fieldName : genResult.getGenOrder()) {
                Sequence sequence = genResult.getSequence(fieldName);
                genSequence.mergeSequence(sequence);
                
                assignTo = new Variable(className + "." + fieldName, null);
                AssignmentStatement statement = new AssignmentStatement(assignTo, sequence.getKeyVariable());
                statement.setFieldDeclClassType(targetTypeName);
                genSequence.addStatement(statement);
              }
            }
            else {
              m_allTypeGenerator.setHashCodeVarMap(prevHashCodeVarMap);
            }
          }
          else {
            // currently, we don't support modifying non-static fields
          }
        }
      }
    }

    return genSequence;
  }
  
  public boolean allFieldsAccessible(Requirement req) {
    boolean allAccessible = true;
    
    HashSet<String> checked = new HashSet<String>();
    Class<?> targetType = Utils.findClass(req.getTargetInstance().getLastRefType());
    for (int i = 0, size = req.getConditions().size(); i < size && allAccessible; i++) {
      if (req.getCondition(i).getConditionTerms().size() > 1) {
        allAccessible = false;
        continue;
      }
      
      BinaryConditionTerm binaryTerm = req.getCondition(i).getOnlyBinaryTerm();
      if (binaryTerm == null || (binaryTerm.getInstance1().isConstant() && 
                                 binaryTerm.getInstance2().isConstant())) {
        continue;
      }
      
      Instance assignTo = binaryTerm.getInstance1();
      assignTo = assignTo.isConstant() ? binaryTerm.getInstance2() : assignTo;
      if (assignTo.isBounded() && assignTo.getRight() != null) { // (v9999.appenderList.elementData @ #!0)
        assignTo = assignTo.getLeft();
      }
      
      // v9999 != null, skip
      if (!assignTo.hasDeclaringInstance()) {
        continue;
      }
      
      // find the first level field
      Instance fieldInstance   = null;
      Instance currentInstance = assignTo;
      while (currentInstance.getLastReference().getDeclaringInstance() != null) {
        fieldInstance   = currentInstance;
        currentInstance = currentInstance.getLastReference().getDeclaringInstance();
        if (currentInstance.isBounded() && currentInstance.getRight() != null) { // (v9999.appenderList.elementData @ #!0)
          currentInstance = currentInstance.getLeft();
        }
      }
      
      // check field
      String fieldName = fieldInstance.getLastRefName();
      if (!checked.contains(fieldName)) {
        Field field = Utils.findClassField(targetType, fieldName);
        allAccessible &= field != null && ((m_accessibility == 0 && Modifier.isPublic(field.getModifiers())) || 
                                           (m_accessibility == 1 && !Modifier.isPrivate(field.getModifiers())));
      }
    }
    
    return allAccessible;
  }
}
