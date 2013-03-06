package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.TestCase.AssignmentStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Statement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

public abstract class AbstractGenerator {

  public AbstractGenerator(Generator allTypeGenerator, int accessibility) {
    m_allTypeGenerator  = allTypeGenerator;
    m_accessibility     = accessibility;
    m_walaAnalyzer      = allTypeGenerator.getWalaAnalyzer();
  }
  
  public abstract Sequence generate(Requirement req, List<Requirement> ancestorReqs);
  
  // try to satisfy the requirement by simple assignments
  protected Sequence trySetDirectly(Requirement req) {
    Variable keyVariable = null;
    List<Statement> statements = new ArrayList<Statement>();

    BinaryConditionTerm term = getReqirementTerm(req);
    if (term != null) {
      Instance instance1 = term.getInstance1();
      Instance instance2 = term.getInstance2();
      
      // instance1 should always be not bounded: v1, v1.field
      if (instance1.getLastReference().getDeclaringInstance() == null) { // v1
        String typeName = instance1.getLastRefType();
        
        Variable assignFrom = null;
        if (Utils.isPrimitiveType(typeName)) { // v1 is primitive
          if (typeName.equals("Z")) {
            assignFrom = new Variable(instance2.getValueWithoutPrefix().equals("0") ? "false" : "true", typeName);
          }
          else if (typeName.equals("C")) {
            char c = (char) Integer.parseInt(instance2.getValueWithoutPrefix());
            String charStr = "'" + (((c == '\\' || c == '\'') ? "\\" : "") + c) + "'";
            assignFrom = new Variable(charStr, typeName);
          }
          else {
            assignFrom = new Variable(instance2.getValueWithoutPrefix(), typeName);
          }
        }
        else { // v1 ==/!= null
          if (term.getComparator() == Comparator.OP_EQUAL && instance2.getValue().equals("null")) {
            String typeName2 = typeName;
            Class<?> clazz = Utils.findClass(typeName);
            if (clazz != null && Modifier.isProtected(clazz.getModifiers())) {
              // Lorg/apache/commons/collections/bidimap/AbstractDualBidiMap$EntrySetIterator
              typeName2 = "L" + typeName.substring(typeName.lastIndexOf('/') + 1);
            }
            assignFrom = new Variable("null", typeName2);
          }
          else if (term.getComparator() == Comparator.OP_INEQUAL && instance2.getValue().equals("null")) {
            if (typeName.equals("Ljava/lang/Class")) {
              assignFrom = new Variable("int.class", typeName);
            }
          }
          else if (instance2.getValue().startsWith("##")) {
            assignFrom = new Variable("\"" + instance2.getValueWithoutPrefix() + "\"", typeName);
          }
        }
        
        if (assignFrom != null) {
          Variable assignTo = new Variable(nextVariableName(), assignFrom.getClassName());
          AssignmentStatement stmt = new AssignmentStatement(assignTo, assignFrom);
          stmt.setOrigAssignToType(typeName);
          statements.add(0, stmt); // the assignment of v1 must be at first
          keyVariable = assignTo;
        }
      }
      else { // v1.field, v1.field1.field2 XXX
        // public fields
      }
    }
    
    Sequence sequence = keyVariable != null ? new Sequence(keyVariable, statements) : null;   
    return sequence;
  }
  
  private BinaryConditionTerm getReqirementTerm(Requirement req) {
    BinaryConditionTerm reqTerm = null;
    if (req.getRequirementTerms().size() == 1) {
      reqTerm = req.getRequirementTerm(0);
    }
    else {
      for (BinaryConditionTerm term : req.getRequirementTerms()) {
        if (term.toString().startsWith("v9999 == ##")) {
          reqTerm = term;
          break;
        }
      }
    }
    return reqTerm;
  }
  
  public List<List<String>> getTargetFields(Requirement req) {
    List<List<String>> targetFields = new ArrayList<List<String>>();
    
    for (BinaryConditionTerm term : req.getRequirementTerms()) {
      List<String> targetFieldLink = new ArrayList<String>();
      Instance currentInstance = term.getInstance1();
      
      //XXX unsound in cases of array: (v9999.elementData @ 0).field != null
      
      while (currentInstance != null && currentInstance.getLastReference() != null && 
             currentInstance.getLastReference().getDeclaringInstance() != null) {
        String fieldName = currentInstance.getLastRefName();
        targetFieldLink.add(0, fieldName);

        currentInstance = currentInstance.getLastReference().getDeclaringInstance();
      }
      if (targetFieldLink.size() > 0) {
        targetFields.add(targetFieldLink);
      }
    }
    return targetFields;
  }
  
  public boolean onlyVarNotNullReq(Requirement req) {
    boolean onlyVarNotNullReq = false;
    if (req != null && req.getRequirementTerms().size() == 1) {
      onlyVarNotNullReq = req.getRequirementTerm(0).toString().equals("v9999 != null");
    }
    return onlyVarNotNullReq;
  }
  
  public WalaAnalyzer getWalaAnalyzer() {
    return m_walaAnalyzer;
  }
  
  public String nextVariableName() {
    return m_allTypeGenerator.getVarNamePool().nextVariableName();
  }
  
  public String thisVariableName() {
    return m_allTypeGenerator.getVarNamePool().thisVariableName();
  }
  
  protected final Generator    m_allTypeGenerator;
  protected final int          m_accessibility;
  protected final WalaAnalyzer m_walaAnalyzer;
}
