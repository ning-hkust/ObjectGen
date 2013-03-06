package hk.ust.cse.ObjectGen.IntraSummary;

import hk.ust.cse.ObjectGen.Summary.Summary;

import java.util.List;

public class IntraSummaryExtractionThread extends Thread {
  
  public IntraSummaryExtractionThread(IntraSummaryExtractor extractor, String methodSig, long maxExtractTime) {
    m_extractor      = extractor;
    m_methodSig      = methodSig;
    m_maxExtractTime = maxExtractTime;
  }
  
  public void run() {
    try {
      m_intraSummaries = m_extractor.extract(m_methodSig, true, m_maxExtractTime);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  
  public List<Summary> getIntraSummaries() {
    return m_intraSummaries;
  }
  
  private final String                  m_methodSig;
  private final long                    m_maxExtractTime;
  private final IntraSummaryExtractor m_extractor;
  private List<Summary> m_intraSummaries;
}
