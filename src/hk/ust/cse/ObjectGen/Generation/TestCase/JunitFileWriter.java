package hk.ust.cse.ObjectGen.Generation.TestCase;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

public class JunitFileWriter {

  public JunitFileWriter(String outputDir) {
    m_outputDir       = outputDir;
    m_buffer          = new char[10485760]; // 10M
    m_testCaseCount   = 0;
  }
  
  public void writeTestCase(String strTestCase, String innerClasses, String pkgName, int modelID, boolean fullyGen) {
    String testFileName = "ObjectGenTest_" + modelID + "_" + (fullyGen ? 1 : 0);

    // create file
    try {
      createNewFile(testFileName, pkgName);
    } catch (IOException e) {
      e.printStackTrace();
      System.err.println("Failed to write test cases to destination!");
    }
    
    // save
    try {
      saveTestCase(strTestCase, innerClasses, testFileName);
    } catch (IOException e) {
      e.printStackTrace();
      System.err.println("Failed to write test cases to destination!");
    }
    
    m_testCaseCount++;
  }
  
  private void saveTestCase(String testCase, String innerClasses, String fileName) throws IOException{
    
    // test case header
    StringBuilder source = new StringBuilder();
    if (testCase != null) {
      source.append("  @Test(timeout=10000) public void test" + m_testCaseCount);
      source.append("() throws Throwable {\n");
      source.append(testCase);
      source.append("  }\n\n");
    }
    
    // write inner class definitions
    source.append(innerClasses); 

    // retrieve content
    File destFile = new File(m_outputDir + "/" + fileName + ".java");
    BufferedReader reader = new BufferedReader(new FileReader(destFile));
    int byteRead = reader.read(m_buffer);
    reader.close();
    
    // save again with the new test case
    BufferedWriter writer = new BufferedWriter(new FileWriter(destFile));
    writer.write(m_buffer, 0, byteRead - 2);
    writer.write(source.toString());
    writer.write("}\n");
    writer.close();
  }
  
  private void createNewFile(String fileName, String pkgName) throws IOException {
    // empty file
    StringBuilder source = new StringBuilder();
    source.append(pkgName.length() > 0 ? "package " + pkgName + ";\n" : "");
    source.append("import junit.framework.*;\n");
    source.append("import org.junit.Test;\n\n");
    source.append("public class " + fileName + " {\n\n");
    source.append("}\n");

    File destFile  = new File(m_outputDir + "/" + fileName + ".java");
    // create java file
    if (!destFile.exists()) {
      destFile.getParentFile().mkdirs();
      destFile.createNewFile();
    }
    
    // save
    BufferedWriter writer = new BufferedWriter(new FileWriter(destFile));
    writer.write(source.toString());
    writer.close();
  }
  
  private final String m_outputDir;
  private final char[] m_buffer;
  private int          m_testCaseCount;
}
