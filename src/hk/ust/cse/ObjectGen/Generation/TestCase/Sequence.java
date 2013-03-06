package hk.ust.cse.ObjectGen.Generation.TestCase;


import hk.ust.cse.ObjectGen.Generation.VarNamePool;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class Sequence {

  public Sequence(Variable keyVariable) {
    m_statements  = new ArrayList<Statement>();
    m_keyVariable = keyVariable; // the key variable is the variable that has the desired object state we want
  }

  public Sequence(Variable keyVariable, List<Statement> statements) {
    m_statements  = statements;
    m_keyVariable = keyVariable;
  }
  
  public void mergeSequence(Sequence sequence) {
    m_statements.addAll(sequence.getStatements());
  }
  
  public void addStatement(Statement statement) {
    m_statements.add(statement);
  }
  
  public void addAssignStatement(Variable assignTo, Variable assignFrom) {
    m_statements.add(new AssignmentStatement(assignTo, assignFrom));
  }
  
  public void addMethod(IR ir, Hashtable<String, Variable> parameters, boolean useInnerClass) {
    List<Variable> allParams = new ArrayList<Variable>();
    boolean keyVarIsParam = false;
    for (int i = 1; i <= ir.getNumberOfParameters(); i++) {
      String varName = "v" + i;
      Variable param = parameters.get(varName);
      allParams.add(param); // could be null
      keyVarIsParam |= param == m_keyVariable;
    }
    InvocationStatement statement = new InvocationStatement(
        ir, allParams, keyVarIsParam ? null : m_keyVariable, useInnerClass);
    m_statements.add(statement);
  }
  
  public List<Statement> getStatements() {
    return m_statements;
  }
  
  public Variable getKeyVariable() {
    return m_keyVariable;
  }
  
  public String toString() {
    StringBuilder str = new StringBuilder();
    for (Statement statement : m_statements) {
      str.append(statement.toString()).append("\n");
    }
    return str.toString();
  }
  
  public Sequence cloneWithNewNames(VarNamePool varNamePool) {
    Hashtable<String, String> clonedVarMap = new Hashtable<String, String>();
    
    List<Statement> clonedStmts = new ArrayList<Statement>();
    for (Statement statement : m_statements) {
      Statement clonedStmt = statement.cloneWithNewNames(varNamePool, clonedVarMap);
      clonedStmts.add(clonedStmt);
    }
    
    String clonedKeyVarName = clonedVarMap.get(m_keyVariable.getVarName());
    return new Sequence(m_keyVariable.cloneWithNewName(clonedKeyVarName), clonedStmts);
  }

  private final Variable        m_keyVariable;
  private final List<Statement> m_statements;
}
