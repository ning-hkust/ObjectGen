package hk.ust.cse.ObjectGen.TestCases;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.VarNamePool;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Reference;

import java.util.HashSet;
import java.util.Hashtable;

public class Account {
  
  public boolean transaction(Transaction t) { 
    if (t.getAmount() > 0) {
      if (t.isDeposit()) {
        return deposit(t);
      }
      else {
        return withdraw(t);
      }
    }
    else {
      return false;
    }
  }
  
  private boolean deposit(Transaction t) {
    m_balance += t.getAmount();
    return true;
  }
  
  private boolean withdraw(Transaction t) {
    if (m_balance - t.getAmount() >= 0) {
      m_balance -= t.getAmount();
      return true;
    }
    else {
      return false;
    }
  }
  
  public void clearBalance() {
    m_balance = 0;
  }
  
  public void printInfo() {
    System.out.println("Balance: " + m_balance);
  }
  
  public static void main(String[] args) throws Exception {
    Reference target = new Reference("v9999", "Lhk/ust/cse/ObjectGen/TestCases/Account", "", new Instance("", null), null, true);
    Instance instance2 = new Instance("#!500", "I", null);
    target.getInstance().setField("m_balance", "I", "", new Instance("", null), true, true);
    Reference fieldRef = target.getInstance().getField("m_balance");
    BinaryConditionTerm term = new BinaryConditionTerm(fieldRef.getInstance(), Comparator.OP_EQUAL, instance2);
    Requirement req = new Requirement(target.getInstance().getLastRefName());
    req.addRequirementTerm(term);
    req.setTargetInstance(target.getInstance(), false);
    
    Generator generator = new Generator("./hk.ust.cse.ObjectGen.jar", 
        null, "./summaries/", new HashSet<String>(), 5, 1, 1, new int[] {0, 0}, true);
    Sequence sequence = generator.generate(req, new VarNamePool(), new Hashtable<Long, String>());
    if (sequence != null) {
      System.out.println(sequence.toString());
    }
    else {
      System.err.println("Failed to generate sequence!");
    }
  }
  
  private int m_balance = 0;
}