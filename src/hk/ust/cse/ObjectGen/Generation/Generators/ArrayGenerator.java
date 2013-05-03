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

import java.lang.reflect.Modifier;
import java.util.Hashtable;
import java.util.List;

public class ArrayGenerator extends AbstractGenerator {

  public ArrayGenerator(Generator allTypeGenerator, int accessibility) {
    super(allTypeGenerator, accessibility);
  }

  @Override
  @SuppressWarnings("unchecked")
  public Sequence generate(Requirement req, List<Requirement> ancestorReqs) {

    // check if the current requirement can be set directly
    Sequence genSequence = trySetDirectly(req);
    
    // if not, generate this array object
    if (genSequence == null) {
      Hashtable<Instance, Requirement> requirementsMap = new Hashtable<Instance, Requirement>();
      Hashtable<String, Instance> indexInstanceMap     = new Hashtable<String, Instance>();
      Requirements childRequirements                   = new Requirements();
      
      int length = 1;
      String arrayTypeName     = null;
      String arrayTypeJavaName = null;
      for (Condition condition : req.getConditions()) {
        BinaryConditionTerm term = condition.getOnlyBinaryTerm();
        if (term == null) {
          continue;
        }
        
        Instance instance1 = term.getInstance1();
        Instance instance2 = term.getInstance2();
        if (!instance1.isBounded() && !instance1.hasDeclaringInstance()) { // v1 != null
          if (arrayTypeName == null) {
            arrayTypeName     = instance1.getLastRefType();
            arrayTypeJavaName = Utils.getClassTypeJavaStr(arrayTypeName);
          }
        }
        else { // v1.length == #!1, (v1 @ #1).length == #!1, (v1 @ #1).field1 != null
          Instance topInstance = instance1.getToppestInstance();
          if (!topInstance.isBounded() && topInstance.getField("length") != null) { // v1.length == #!1
            if (instance2.getValueWithoutPrefix().contains("|")) { // multiple model values
              // we have no choice but to choose one value, this may cause unsoundness
              String valueStr = instance2.getValueWithoutPrefix();
              length = Integer.parseInt(valueStr.substring(0, valueStr.indexOf('|')));
            }
            else {
              length = Integer.parseInt(instance2.getValueWithoutPrefix());
            }
            
            if (arrayTypeName == null) {
              arrayTypeName     = instance1.getToppestInstance().getLastRefType();
              arrayTypeJavaName = Utils.getClassTypeJavaStr(arrayTypeName);
            }
          }
          else if (topInstance.isBounded() && topInstance.getRight() != null) { // v1 @ #!1 != null, (v1 @ #1).field1 != null
            // handle situations like: ((v9999 @ #!0).value @ #!0) == #!45
            boolean isIndexInstance = true;
            Instance currentTop = topInstance;
            while (currentTop != null && isIndexInstance) {
              Requirement childReq = requirementsMap.get(currentTop);
              if (childReq != null) {
                childReq.addCondition(condition);
                isIndexInstance = false;
              }
              else {
                topInstance = currentTop.getRight() != null ? currentTop : topInstance;
                currentTop = currentTop.getLeft();
                currentTop = currentTop != null ? currentTop.getToppestInstance() : currentTop;
              }
            }
            if (!isIndexInstance) {
              continue;
            }
            
            // try to get the index
            String indexValue = topInstance.getRight().computeArithmetic();
            Instance instance = indexInstanceMap.get(indexValue);
            if (instance == null) {
              instance = new Instance("", null);
              indexInstanceMap.put(indexValue, instance);
              
              // make instance v9999 (default name for target)
              Reference lastRef = topInstance.getLeft().getLastReference();
              String elemType = lastRef.getType().startsWith("[") ? lastRef.getType().substring(1) : "Unknown-Type";
              if (topInstance.getType() != null && (elemType.equals("Unknown-Type") || 
                                                    Utils.isSubClass(elemType, topInstance.getType()))) {
                elemType = topInstance.getType();
              }
              
              // convert (v1 @ #1) to v9999, such that it becomes a non-array problem
              new Reference("v9999", elemType, lastRef.getCallSites(), instance, null, true);
              for (Reference fieldRef : topInstance.getFields()) {
                instance.setField(fieldRef.getName(), fieldRef.getType(), 
                    fieldRef.getCallSites(), fieldRef.getInstances(), true, true);
              }
            }
            else {
              // convert (v1 @ #1) to v9999, such that it becomes a non-array problem
              for (Reference fieldRef : topInstance.getFields()) {
                instance.setField(fieldRef.getName(), fieldRef.getType(), 
                    fieldRef.getCallSites(), fieldRef.getInstances(), true, true);
              }
            }
            
            Requirement childReq = requirementsMap.get(instance);
            if (childReq == null) {
              childReq = new Requirement(indexValue);
              childReq.setTargetInstance(instance, false);
              requirementsMap.put(instance, childReq);
              childRequirements.addRequirement(indexValue, childReq);
            }
            
            if (instance1 == topInstance) {
              term = new BinaryConditionTerm(instance, term.getComparator(), instance2);
            }
            childReq.addCondition(new Condition(term));
          }
          else { // v9999.field1 == #!1
            Requirement childReq = requirementsMap.get(topInstance);
            if (childReq != null) {
              childReq.addCondition(new Condition(term));
            }
          }
        }
      }

      // get the inner type
      Class<?> arrayTypeClass = Utils.findClass(arrayTypeName);
      if (arrayTypeClass != null) {
        if ((m_accessibility == 0 && Modifier.isPublic(arrayTypeClass.getModifiers() /* component modifier */ )) || 
            (m_accessibility == 1) && !Modifier.isPrivate(arrayTypeClass.getModifiers() /* component modifier */)) { 

          // generate recursively for the child requirements
          Hashtable<Long, String> prevHashCodeVarMap = 
              (Hashtable<Long, String>) m_allTypeGenerator.getHashCodeVarMap().clone();
          GenerationResult genResult = m_allTypeGenerator.gen4ChildReqs(childRequirements, ancestorReqs);
          
          if (!genResult.hasNotSat()) {
            // for non-public class, we will use inner class
            String elemTypeJavaName = null;
            String arrayTypeName2   = null;
            if (!Modifier.isPublic(arrayTypeClass.getModifiers())) {
              // [Lorg/apache/commons/collections/bidimap/AbstractDualBidiMap$EntrySetIterator
              arrayTypeName2   = "[L" + arrayTypeName.substring(arrayTypeName.lastIndexOf('/') + 1);
              elemTypeJavaName = arrayTypeName.substring(arrayTypeName.lastIndexOf('/') + 1);
              elemTypeJavaName = elemTypeJavaName.replace('$', '.');
            }
            else {
              // get the inner type name
              arrayTypeName2   = arrayTypeName;
              elemTypeJavaName = arrayTypeJavaName.endsWith("[]") ? 
                  arrayTypeJavaName.substring(0, arrayTypeJavaName.length() - 2) : arrayTypeJavaName;
            }
            
            // convert new Object[][1] -> new Object[1][1]
            String elemTypeToInit = elemTypeJavaName;
            elemTypeToInit = elemTypeToInit.endsWith("[]") ? 
                elemTypeToInit.substring(0, elemTypeToInit.length() - 2) + "[" + length + "]" : elemTypeToInit;
            
            // create variables
            Variable assignTo   = new Variable(nextVariableName(), arrayTypeName2);
            Variable assignFrom = new Variable("new " + elemTypeToInit + "[" + length + "]", arrayTypeName2);
            
            // create new array statement
            genSequence = new Sequence(assignTo);
            AssignmentStatement statement = new AssignmentStatement(assignTo, assignFrom);
            statement.setOrigAssignToType(arrayTypeName);
            genSequence.addStatement(statement);
      
            // create assignment statements for each index
            String varName = thisVariableName();
            for (String index : genResult.getGenOrder()) {
              Sequence sequence = genResult.getSequence(index);
              genSequence.mergeSequence(sequence);
              
              assignTo = new Variable(varName + "[" + index.substring(2) + "]", null);
              genSequence.addAssignStatement(assignTo, sequence.getKeyVariable());
            }
          }
          else {
            m_allTypeGenerator.setHashCodeVarMap(prevHashCodeVarMap);
          }
        }
      }
    }

    return genSequence;
  }
}
