package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.TestCase.AssignmentStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Statement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
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
      if (instance1.isConstant()) { // null != v1
        instance1 = term.getInstance2();
        instance2 = term.getInstance1();
      }
      
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
          if (term.isEqualToNull()) {
            String typeName2 = typeName;
            Class<?> clazz = Utils.findClass(typeName);
            if (clazz != null && Modifier.isProtected(clazz.getModifiers())) {
              // Lorg/apache/commons/collections/bidimap/AbstractDualBidiMap$EntrySetIterator
              typeName2 = "L" + typeName.substring(typeName.lastIndexOf('/') + 1);
            }
            assignFrom = new Variable("null", typeName2);
          }
          else if (term.isNotEqualToNull()) {
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
    if (req.getConditions().size() == 1) {
      reqTerm = req.getCondition(0).getOnlyBinaryTerm();
    }
    else {
      for (Condition reqCond : req.getConditions()) {
        BinaryConditionTerm binaryTerm = reqCond.getOnlyBinaryTerm();
        if (binaryTerm != null && binaryTerm.toString().startsWith("v9999 == ##")) {
          reqTerm = binaryTerm;
          break;
        }
      }
    }
    return reqTerm;
  }

  // obtain the fields in req
  public List<List<String>> getTargetFields(Requirement req) {
    List<List<String>> targetFields = new ArrayList<List<String>>();
    
    for (Condition condition : req.getConditions()) {
      for (ConditionTerm term : condition.getConditionTerms()) {
        for (Instance instance : term.getInstances()) {
          //XXX unsound in cases of array: (v9999.elementData @ 0).field != null

          String[] fieldNames = instance.getDeclFieldNames();
          if (fieldNames.length > 0) {
            targetFields.add(Arrays.asList(fieldNames));
          }
        }
      }
    }
    return targetFields;
  }
  
  public boolean onlyVarNullReq(Requirement req, String varName) {
    return onlyVarNullOrNotNullReq(req, varName, false);
  }
  
  public boolean onlyVarNotNullReq(Requirement req, String varName) {
    return onlyVarNullOrNotNullReq(req, varName, true);
  }
  
  private boolean onlyVarNullOrNotNullReq(Requirement req, String varName, boolean notNull) {
    // ignore type conditions
    List<Condition> nonTypeConditions = new ArrayList<Condition>();
    for (Condition condition : req.getConditions()) {
      if (condition.getOnlyTypeTerm() == null) {
        nonTypeConditions.add(condition);
      }
    }

    boolean onlyVarNullOrNotNullReq = false;
    if (nonTypeConditions.size() > 0) {
      onlyVarNullOrNotNullReq = true;
      String comp = notNull ? " != " : " == ";
      for (int i = 0, size = nonTypeConditions.size(); i < size && onlyVarNullOrNotNullReq; i++) {
        BinaryConditionTerm term = nonTypeConditions.get(i).getOnlyBinaryTerm();
        String termStr = term != null ? term.toString() : null;
        onlyVarNullOrNotNullReq &= termStr != null && 
            (termStr.equals(varName + comp + "null") || termStr.equals("null" + comp + varName));
      }
    }
    return onlyVarNullOrNotNullReq;
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
