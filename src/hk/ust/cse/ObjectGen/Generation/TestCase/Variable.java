package hk.ust.cse.ObjectGen.Generation.TestCase;

import hk.ust.cse.util.Utils;

public class Variable {
  // clsName should not have been java-tified
  public Variable(String varName, String clsName) {
    m_varName = varName;
    m_clsName = clsName;
    m_clsJavaName = m_clsName != null ? Utils.getClassTypeJavaStr(m_clsName) : null;
  }
  
  public String getClassName() {
    return m_clsName;
  }
  
  public String getClassJavaName() {
    return m_clsJavaName;
  }
  
  public String getVarName() {
    return m_varName;
  }
  
  public Variable cloneWithNewName(String newName) {
    return new Variable(newName, m_clsName);
  }
  
  private final String m_clsName;
  private final String m_clsJavaName;
  private final String m_varName;
}
