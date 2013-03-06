package hk.ust.cse.ObjectGen.Generation.TestCase;

import hk.ust.cse.ObjectGen.Generation.VarNamePool;

import java.util.Hashtable;
import java.util.List;

public class AssignmentStatement extends Statement {

  public AssignmentStatement(Variable assignTo, Variable assignFrom) {
    m_variables.add(assignTo);
    m_variables.add(assignFrom);
  }
  
  public void setOrigAssignToType(String assignToType) {
    // in case assignTo's type has been changed to inner type
    m_assignToType = assignToType;
  }
  
  public void setFieldDeclClassType(String declClassType) {
    m_declClassType = declClassType;
  }
  
  public Variable getAssignTo() {
    return m_variables.get(0);
  }
  
  public Variable getAssignFrom() {
    return m_variables.get(1);
  }
  
  public String getOrigAssignToType() {
    return m_assignToType;
  }
  
  public String getFieldDeclClassType() {
    return m_declClassType;
  }
  
  public String toString() {
    Variable assignTo   = getAssignTo();
    Variable assignFrom = getAssignFrom();

    String className = assignTo.getClassName();
    String visibleName = null;
    if (className != null) {
      boolean arrayType = className.startsWith("[");
      className = arrayType ? className.substring(1) : className;
      
      visibleName = visibleClassName(className);
      visibleName = arrayType ? visibleName + "[]" : visibleName;
    }

    StringBuilder str = new StringBuilder("    ");
    if (visibleName != null && visibleName.length() > 0) {
      str.append(visibleName).append(" ");
    }
    str.append(assignTo.getVarName()).append(" = ");
    if (visibleName != null && visibleName.length() > 0) {
      str.append("(").append(visibleName).append(") ");
    }
    str.append(assignFrom.getVarName()).append(";");
    return str.toString();
  }
  
  @Override
  public Statement cloneWithNewNames(VarNamePool varNamePool, Hashtable<String, String> clonedVarMap) {
    List<Variable> clonedVariables = cloneVarsWithNewNames(varNamePool, clonedVarMap);
    
    AssignmentStatement cloned = new AssignmentStatement(clonedVariables.get(0), 
                                                         clonedVariables.get(1));
    cloned.setFieldDeclClassType(m_declClassType);
    cloned.setOrigAssignToType(m_assignToType);
    return cloned;
  }
  
  private String m_assignToType;  // only useful when we assigning to a non-public variable
  private String m_declClassType; // only useful when we assign to a non-public field
}
