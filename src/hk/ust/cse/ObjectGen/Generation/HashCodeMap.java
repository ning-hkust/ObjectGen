package hk.ust.cse.ObjectGen.Generation;

import java.util.Enumeration;
import java.util.Hashtable;

public class HashCodeMap {

  public HashCodeMap() {
    m_hashCodeVarMap = new Hashtable<Long, String>();
  }
  
  public String getVarName(long hashCode) {
    return m_hashCodeVarMap.get(hashCode);
  }
  
  public void putVarName(long hashCode, String varName) {
    m_hashCodeVarMap.put(hashCode, varName);
  }
  
  public HashCodeMap clone() {
    HashCodeMap clone = new HashCodeMap();
    Enumeration<Long> keys = m_hashCodeVarMap.keys();
    while (keys.hasMoreElements()) {
      Long key = (Long) keys.nextElement();
      clone.m_hashCodeVarMap.put(key, m_hashCodeVarMap.get(key));
    }
    return clone;
  }
  
  private final Hashtable<Long, String> m_hashCodeVarMap;
}
