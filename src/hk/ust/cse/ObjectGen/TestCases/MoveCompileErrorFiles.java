package hk.ust.cse.ObjectGen.TestCases;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;

public class MoveCompileErrorFiles {

  public static void main(String[] args) {
    HashSet<String> errorList = new HashSet<String>();
    try {
      BufferedReader reader = new BufferedReader(new FileReader("D:/Projects/ObjectGen/experiments/apache-commons-collections/runtests/error.txt"));
      String line = null;
      while ((line = reader.readLine()) != null) {
        int index1 = line.indexOf("ObjectGenTest_");
        int index2 = line.indexOf(".java", index1);
        if (index1 >= 0 && index2 > index1) {
          String fileName = line.substring(index1, index2 + 5);
          errorList.add(fileName);
        }
      }
      reader.close();
    } catch (IOException e) {}

    int moved = 0;
    File filesDir = new File("D:/Projects/ObjectGen/experiments/apache-commons-collections/runtests/objGenTests");
    File errorDir = new File("D:/Projects/ObjectGen/experiments/apache-commons-collections/runtests/objGenTests_error");
    errorDir.mkdirs();
    for (String fileName : errorList) {
      File file = new File(filesDir, fileName);
      if (file.exists()) {
        file.renameTo(new File(errorDir, fileName));
        moved++;
      }
    }
    System.out.println(moved + " moved!");
  }
}
