package hk.ust.cse.ObjectGen.TestCases;

public class Transaction { 
  public Transaction(int amount, boolean type) throws Exception {
    if (amount < 0) {
      throw new Exception("Invalid amount.");
    }
    m_amount = amount;
    m_type = type;
  }
  
  public int getAmount() {
    return m_amount;
  }
  
  public boolean isDeposit() {
    return m_type;
  }

  private int m_amount;
  private boolean m_type;
} 