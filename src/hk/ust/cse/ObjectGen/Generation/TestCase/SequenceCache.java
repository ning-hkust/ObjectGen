package hk.ust.cse.ObjectGen.Generation.TestCase;

import hk.ust.cse.ObjectGen.Generation.Requirement;

import java.util.HashMap;

public class SequenceCache {

  public SequenceCache() {
    m_cache = new HashMap<Object[], Sequence>(); // HashMap permits null value
  }
  
  public boolean requirementsCached(Requirement req, int step) {
    return m_cache.containsKey(new Object[] {req, step});
  }
  
  public Sequence getSequence(Requirement req, int step) {
    return m_cache.get(new Object[] {req, step});
  }
  
  public void saveSequence(Requirement req, int step, Sequence seq) {
    m_cache.put(new Object[] {req, step}, seq);
  }
  
  private HashMap<Object[], Sequence> m_cache; // Requirement + stepLevel -> Sequence
}
