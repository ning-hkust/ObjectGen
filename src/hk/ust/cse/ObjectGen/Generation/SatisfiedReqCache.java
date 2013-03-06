package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;

import java.util.Hashtable;

public class SatisfiedReqCache {

  public SatisfiedReqCache() {
    m_cache = new Hashtable<Requirement, Sequence>();
  }
  
  public Sequence findSequence(Requirement req) {
    return m_cache.get(req);
  }
  
  public void saveSequence(Requirement req, Sequence seq) {
    m_cache.put(req, seq);
  }
  
  private final Hashtable<Requirement, Sequence> m_cache;
}
