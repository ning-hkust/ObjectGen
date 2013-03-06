package hk.ust.cse.ObjectGen.Generation;

public class VarNamePool {

  public VarNamePool() {
    m_varCounter = 0;
  }
  
  public String nextVariableName() {
    return "v" + ++m_varCounter;
  }
  
  public String thisVariableName() {
    return "v" + m_varCounter;
  }

  private int m_varCounter;
}
