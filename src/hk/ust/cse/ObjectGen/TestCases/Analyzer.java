package hk.ust.cse.ObjectGen.TestCases;

import hk.ust.cse.util.DbHelper.DbHelperSqlite;

import java.io.File;
import java.sql.Connection;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;


public class Analyzer {
  
  Analyzer(String dbPath, String gentestsDir) {
    m_dbPath = dbPath;
    
    // read model test files
    m_generateMap = new Hashtable<Integer, Boolean>();
    readGeneratedFiles(new File(gentestsDir));
    
    // read branchfirstline model information
    m_branchModelMap     = new Hashtable<Integer, List<Integer>>();
    m_branchFirstLineIds = new ArrayList<Integer>();
    readBranchFirstLineModelMapping();
  }
  
  private void readGeneratedFiles(File dir) {
    for (File file : dir.listFiles()) {
      if (file.isDirectory()) {
        readGeneratedFiles(file);
      }
      else {
        if (file.getName().matches("ObjectGenTest_[0-9]+_[01]\\.java")) {
          String fileName = file.getName();
          int index = fileName.lastIndexOf("_");
          
          String modelId = fileName.substring(14, index);
          boolean result = fileName.substring(index + 1, fileName.length() - 5).equals("1");
          m_generateMap.put(Integer.parseInt(modelId), result);
        }
      }
    }
  }
  
  private void readBranchFirstLineModelMapping() {
    Connection conn = null;
    try {
      conn = DbHelperSqlite.openConnection(m_dbPath);

      // select all non-covered branches' first line
      String sqlText = "Select * From Model";
      ResultSet rs = DbHelperSqlite.executeQuery(conn, sqlText);
      while (rs.next()) {
        int modelId           = rs.getInt(1);
        int branchFirstLineId = rs.getInt(2);
        List<Integer> modelIds = m_branchModelMap.get(branchFirstLineId);
        if (modelIds == null) {
          modelIds = new ArrayList<Integer>();
          m_branchModelMap.put(branchFirstLineId, modelIds);
          m_branchFirstLineIds.add(branchFirstLineId);
        }
        modelIds.add(modelId);
      }
      rs.close();
    } catch (Exception e) {
      e.printStackTrace();
    } finally {
      DbHelperSqlite.closeConnection(conn);
    }
  }
  
  public void calBranchFirstLineSuccessRate() {
    int totalSucceeded = 0;
    for (Integer brachFirstLineId : m_branchFirstLineIds) {
      List<Integer> modelIds = m_branchModelMap.get(brachFirstLineId);
      
      boolean succeeded = false;
      for (int i = 0, size = modelIds.size(); i < size && !succeeded; i++) {
        Boolean result = m_generateMap.get(modelIds.get(i));
        succeeded = result != null && result.booleanValue();
      }
      totalSucceeded += succeeded ? 1 : 0;
    }
    
    System.out.println("Success Rate: " + totalSucceeded + " / " + m_branchFirstLineIds.size() + 
        " = " + ((double) totalSucceeded / (double) m_branchFirstLineIds.size()));
  }
  
  public static void main(String[] args) {
    Analyzer analyzer = new Analyzer("D:/Projects/ObjectGen/experiments/apache-commons-collections/BranchModel", 
                                     "D:/Projects/ObjectGen/experiments/apache-commons-collections/runtests/results");
//    Analyzer analyzer = new Analyzer("D:/Projects/ObjectGen/experiments/apache-commons-math/BranchModel", 
//                                     "D:/Projects/ObjectGen/experiments/apache-commons-math/runtests/results");
//    Analyzer analyzer = new Analyzer("D:/Projects/ObjectGen/experiments/JSAP/BranchModel", 
//                                     "D:/Projects/ObjectGen/experiments/JSAP/runtests/results");
//    Analyzer analyzer = new Analyzer("D:/Projects/ObjectGen/experiments/sat4j/BranchModel", 
//                                     "D:/Projects/ObjectGen/experiments/sat4j/runtests/results");
    analyzer.calBranchFirstLineSuccessRate();
  }
  
  private final String                            m_dbPath;
  private final Hashtable<Integer, Boolean>       m_generateMap;
  private final Hashtable<Integer, List<Integer>> m_branchModelMap;
  private final List<Integer>                     m_branchFirstLineIds;
}
