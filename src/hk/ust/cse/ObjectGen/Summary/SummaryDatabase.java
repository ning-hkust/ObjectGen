package hk.ust.cse.ObjectGen.Summary;

import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.Utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class SummaryDatabase {

  public SummaryDatabase(String databasePath, int maxCache, WalaAnalyzer walaAnalyzer) {
    m_maxCache       = maxCache;
    m_databasePath   = databasePath;
    m_walaAnalyzer   = walaAnalyzer;
    m_usedSequence   = new ArrayList<String>();
    m_summaryCache = new Hashtable<String, List<Summary>>();
  }
  
  public void saveSummariesOverride(String methodSig, List<Summary> summaries) {
    // create full directory name
    String methodName      = methodSig.substring(0, methodSig.indexOf('('));
    String slashMethodName = methodName.replace('.', '/').replace('<', '(').replace('>', ')');
    String fullDirPath     = m_databasePath + "/" + slashMethodName + "_" + methodSig.hashCode();
    
    // create directory
    File directory = new File(fullDirPath);
    if (directory.exists()) { // always create a new one
      Utils.deleteFile(directory);
    }
    directory.mkdirs();
    
    // save summaries, one summary per file
    for (int i = 0, size = summaries.size(); i < size; i++) {
      try {
        BufferedWriter writer = new BufferedWriter(new FileWriter(fullDirPath + "/" + i));
        String persistentString = summaries.get(i).toPersistentString();
        writer.write(persistentString);
        writer.close();
      } catch (Exception e) {
        e.printStackTrace();
        // continue
      }
    }
  }
  
  public void saveSummariesAppend(String methodSig, List<Summary> summaries, int startingIndex) {
    // create full directory name
    String methodName      = methodSig.substring(0, methodSig.indexOf('('));
    String slashMethodName = methodName.replace('.', '/').replace('<', '(').replace('>', ')');
    String fullDirPath     = m_databasePath + "/" + slashMethodName + "_" + methodSig.hashCode();

    // create directory
    File directory = new File(fullDirPath);
    if (startingIndex == 0 && directory.exists()) { // create a new one if start from 0
      Utils.deleteFile(directory);
    }
    if (!directory.exists()) {
      directory.mkdirs();
    }
    
    // save summaries, one summary per file
    for (int i = startingIndex, size = summaries.size(); i < size; i++) {
      try {
        BufferedWriter writer = new BufferedWriter(new FileWriter(fullDirPath + "/" + i));
        String persistentString = summaries.get(i).toPersistentString();
        writer.write(persistentString);
        writer.close();
      } catch (Exception e) {
        e.printStackTrace();
        // continue
      }
    }
  }
  
  public void removeSummaries(String methodSig) {
    // create full directory name
    String methodName      = methodSig.substring(0, methodSig.indexOf('('));
    String slashMethodName = methodName.replace('.', '/').replace('<', '(').replace('>', ')');
    String fullDirPath     = m_databasePath + "/" + slashMethodName + "_" + methodSig.hashCode();
    
    // delete directory
    File directory = new File(fullDirPath);
    if (directory.exists()) { // always create a new one
      Utils.deleteFile(directory);
    }
  }
  
  // XXX should support jar file also!!!
  public int readSummaryCount(String methodSig) {
    int count = 0;
    
    List<Summary> cached = m_summaryCache.get(methodSig);
    if (cached == null) {
      // create full directory name
      String methodName      = methodSig.substring(0, methodSig.indexOf('('));
      String slashMethodName = methodName.replace('.', '/').replace('<', '(').replace('>', ')');
      String fullDirPath     = m_databasePath + "/" + slashMethodName + "_" + methodSig.hashCode();
      
      // check folder
      File directory = new File(fullDirPath);
      if (directory.exists() && directory.isDirectory()) {
        count = directory.listFiles().length;
      }
    }
    else {
      count = cached.size();
    }
    
    return count;
  }
  
  // XXX should support jar file also!!!
  public List<Summary> readSummaries(String methodSig) {
    List<Summary> summaries = null;
    
    List<Summary> cached = m_summaryCache.get(methodSig);
    if (cached == null) {
      // create full directory name
      String methodName      = methodSig.substring(0, methodSig.indexOf('('));
      String slashMethodName = methodName.replace('.', '/').replace('<', '(').replace('>', ')');
      String fullDirPath     = m_databasePath + "/" + slashMethodName + "_" + methodSig.hashCode();
      
      // check folder
      File directory = new File(fullDirPath);
      if (!directory.exists() || !directory.isDirectory()) {
        return null;
      }
      
      // get summary files
      summaries = new ArrayList<Summary>();
      char[] buff = new char[10485760]; // 10M
      File[] files = directory.listFiles();
      for (File file : files) {
        try {
          // read persistent string from file
          BufferedReader reader = new BufferedReader(new FileReader(file));
          int byteRead = reader.read(buff);
          String persistentString = new String(buff, 0, byteRead);
          
          // create summary from persistent string
          Summary summary = Summary.fromPersistentString(persistentString, m_walaAnalyzer);
          if (summary != null) {
            summaries.add(summary);
          }
          reader.close();
        } catch (Exception e) {
          e.printStackTrace();
          // continue
        }
      }
      
      // save this summary list to cache
      if (m_summaryCache.size() >= m_maxCache) {
        m_summaryCache.remove(m_usedSequence.get(0));
        m_usedSequence.remove(0);
      }
      m_usedSequence.add(methodSig);
      m_summaryCache.put(methodSig, summaries);
    }
    else {
      summaries = new ArrayList<Summary>();
      for (Summary summary : cached) {
        summaries.add(summary.deepClone());
      }
      m_usedSequence.remove(methodSig);
      m_usedSequence.add(methodSig);
    }
    
    return summaries;
  }
  
  public void removeFromCache(String methodSig) {
    m_summaryCache.remove(methodSig);
  }
  
  public List<Summary> refreshCache(String methodSig) {
    removeFromCache(methodSig);
    return readSummaries(methodSig);
  }
  
  private final int                              m_maxCache;
  private final String                           m_databasePath;
  private final WalaAnalyzer                     m_walaAnalyzer;
  private final List<String>                     m_usedSequence;
  private final Hashtable<String, List<Summary>> m_summaryCache;
}
