package hk.ust.cse.ObjectGen.Summary;

import java.util.HashSet;

public class SummaryExtractionThread extends Thread {
  
  public SummaryExtractionThread(SummaryExtractor extractor, String methodSig, long maxExtractTime, 
      HashSet<String> allMethodSet, HashSet<String> filterSet, HashSet<String> extractedSet) {
    m_extractor      = extractor;
    m_methodSig      = methodSig;
    m_maxExtractTime = maxExtractTime;
    m_allMethodSet   = allMethodSet;
    m_filterSet      = filterSet;
    m_extractedSet   = extractedSet;
  }
  
  public void run() {
    try {
      m_extractor.extract(m_methodSig, true, m_maxExtractTime, m_allMethodSet, m_filterSet, m_extractedSet);
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
  
  private final SummaryExtractor m_extractor;
  private final long             m_maxExtractTime;
  private final String           m_methodSig;
  private final HashSet<String>  m_allMethodSet;
  private final HashSet<String>  m_filterSet;
  private final HashSet<String>  m_extractedSet;
}
