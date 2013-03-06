package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class GenerationResult {

  public GenerationResult() {
    m_notSatVarNames  = new ArrayList<String>();
    m_generatingOrder = new ArrayList<String>();
    m_sequences       = new Hashtable<String, Sequence>();
  }
  
  public void addSequence(String varName, Sequence sequence) {
    m_generatingOrder.add(varName);
    m_sequences.put(varName, sequence);
  }
  
  public void addNotSat(String varName) {
    m_notSatVarNames.add(varName);
  }
  
  public List<String> getGenOrder() {
    return m_generatingOrder;
  }
  
  public Sequence getSequence(String varName) {
    return m_sequences.get(varName);
  }
  
  public int getSequenceCount() {
    return m_sequences.size();
  }
  
  public List<String> getNotSatVarNames() {
    return m_notSatVarNames;
  }
  
  public boolean hasNotSat() {
    return m_notSatVarNames.size() > 0;
  }
  
  private final List<String> m_notSatVarNames;
  private final List<String> m_generatingOrder;
  private final Hashtable<String, Sequence> m_sequences;
}
