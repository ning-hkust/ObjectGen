package hk.ust.cse.ObjectGen.Summary.MethodList;

import hk.ust.cse.Prevision.InstructionHandlers.CompleteForwardHandler;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.Solver.SMTChecker.SOLVERS;
import hk.ust.cse.Prevision.VirtualMachine.Executor.ForwardExecutor;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;

public class MethodListExtractor {

  public MethodListExtractor(String appJar, String pseudoImplJar) throws Exception {
    m_executor = new ForwardExecutor(appJar, pseudoImplJar, new CompleteForwardHandler(), new SMTChecker(SOLVERS.Z3));
  }
  
  public void produceNotExtractMethodList(List<String> allowPrefix) {
    List<String> allMethods = findAllMethods(allowPrefix);
    HashSet<String> fullExtractedMethods = new HashSet<String>();
    HashSet<String> partialExtractedMethods = new HashSet<String>();
    
    try {
      BufferedReader reader = new BufferedReader(new FileReader("./summaries/full_extract_methods.txt"));
      String line1 = null;
      while ((line1 = reader.readLine()) != null) {
        fullExtractedMethods.add(line1);
      }
      reader.close();
    } catch (IOException e) {}
    
    try {
      BufferedReader reader = new BufferedReader(new FileReader("./summaries/partial_extract_methods.txt"));
      String line1 = null;
      while ((line1 = reader.readLine()) != null) {
        partialExtractedMethods.add(line1);
      }
      reader.close();
    } catch (IOException e) {}
    
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter("./summaries/not_extract_methods.txt"));
      for (String methodSig : allMethods) {
        if (!fullExtractedMethods.contains(methodSig) && !partialExtractedMethods.contains(methodSig)) {
          writer.append(methodSig).append("\n");
        }
      }
      writer.close();
    } catch (IOException e) {}
  }
  
  public void produceNotFullExtractMethodList(List<String> allowPrefix) {
    List<String> allMethods = findAllMethods(allowPrefix);
    HashSet<String> fullExtractedMethods = new HashSet<String>();
    
    try {
      BufferedReader reader = new BufferedReader(new FileReader("./summaries/full_extract_methods.txt"));
      String line1 = null;
      while ((line1 = reader.readLine()) != null) {
        fullExtractedMethods.add(line1);
      }
      reader.close();
    } catch (IOException e) {}
    
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter("./summaries/not_full_extract_methods.txt"));
      for (String methodSig : allMethods) {
        if (!fullExtractedMethods.contains(methodSig)) {
          writer.append(methodSig).append("\n");
        }
      }
      writer.close();
    } catch (IOException e) {}
  }

  public void produceAllMethodList(List<String> allowPrefix) {
    List<String> allMethods = findAllMethods(allowPrefix);
    
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter("./summaries/all_methods.txt"));
      for (String methodSig : allMethods) {
        writer.append(methodSig).append("\n");
      }
      writer.close();
    } catch (IOException e) {}
  }
  
  private List<String> findAllMethods(List<String> allowPrefix) {
    HashSet<String> allMethods = new HashSet<String>();
    // enumerate all classes
    Iterator<IClass> classes = m_executor.getWalaAnalyzer().getClassHierarchy().iterator();
    while (classes.hasNext()) {
      IClass aClass = (IClass) classes.next();

      // enumerate all methods
      Iterator<IMethod> methods = aClass.getAllMethods().iterator();
      while (methods.hasNext()) {
        IMethod method = methods.next();

        // remove abstract and native methods
        String methodSig = method.getSignature();
        if (!method.isAbstract() && !method.isNative() && isPrefixOf(methodSig, allowPrefix)) {
          allMethods.add(methodSig);
        }
      }
    }
    
    // sort
    List<String> allMethodList = new ArrayList<String>();
    for (String method : allMethods) {
      allMethodList.add(method);
    }
    Collections.sort(allMethodList);
    
    return allMethodList;
  }
  
  private boolean isPrefixOf(String methodSig, List<String> allowPrefix) {
    boolean isPrefix = false;
    for (int i = 0, size = allowPrefix.size(); i < size && !isPrefix; i++) {
      if (methodSig.startsWith(allowPrefix.get(i))) {
        isPrefix = true;
      }
    }
    return isPrefix;
  }
  
  public static void main(String[] args) throws Exception {
    MethodListExtractor extractor = new MethodListExtractor(
        //"../../BranchModelGenerator/targets/apache-commons-collections/target/commons-collections-3.2.1.jar", 
        //"../../BranchModelGenerator/targets/apache-commons-math/target/commons-math-2.1.jar", 
        //"../../BranchModelGenerator/targets/JSAP/target/JSAP-2.1.jar", 
        //"../../BranchModelGenerator/targets/sat4j/target/org.sat4j.core-2.2.0.jar", 
        "../../STAR/experiments/ObjectGen/apache-commons-collections/targets/commons-collections-4.0-r1351903.jar", 
        //"../../STAR/experiments/ObjectGen/apache-log4j/targets/log4j-1.0.4.jar", 
        //"../../STAR/experiments/ObjectGen/apache-ant/targets/ant-all-1.6.2.jar", 
        //"../../STAR/experiments/ObjectGen/crawler4j/targets/crawler4j-3.3.jar", 
        //"../../STAR/experiments/ObjectGen/aspectj/targets/aspectjtools-1.1.0.jar", 
        "./lib/hk.ust.cse.Prevision_PseudoImpl.jar");

    List<String> allowPrefix = new ArrayList<String>();
//    allowPrefix.add("java.lang.Boolean");
//    allowPrefix.add("java.lang.Byte");
//    allowPrefix.add("java.lang.Character."); // avoid CharacterData
//    allowPrefix.add("java.lang.Double");
//    allowPrefix.add("java.lang.Enum");
//    allowPrefix.add("java.lang.Float");
//    allowPrefix.add("java.lang.Integer");
//    allowPrefix.add("java.lang.Long");
//    allowPrefix.add("java.lang.Number");
//    allowPrefix.add("java.lang.Object");
//    allowPrefix.add("java.lang.Short");
//    allowPrefix.add("java.lang.String");
//    allowPrefix.add("java.lang.StringBuffer");
//    allowPrefix.add("java.lang.StringBuilder");
//    allowPrefix.add("java.lang.Math");
//    allowPrefix.add("java.util.Abstract");
//    allowPrefix.add("java.util.Array");
//    allowPrefix.add("java.util.Hash");
//    allowPrefix.add("java.util.Linked");
//    //allowPrefix.add("java.util.Tree");
//    allowPrefix.add("java.util.TreeMap.<init>()V");
//    allowPrefix.add("java.util.TreeSet.<init>()V");
//    allowPrefix.add("java.util.Vector");
//    allowPrefix.add("java.util.Properties");
//    allowPrefix.add("java.io.OutputStream");
//    allowPrefix.add("java.io.InputStream");
//    allowPrefix.add("java.io.FilterOutputStream");
//    allowPrefix.add("java.io.ByteArrayOutputStream");
//    allowPrefix.add("java.io.ByteArrayInputStream");
//    allowPrefix.add("java.io.Writer");
//    allowPrefix.add("java.io.FilterWriter");
//    allowPrefix.add("java.io.CharArrayWriter");
//    allowPrefix.add("java.io.StringWriter");
//    allowPrefix.add("java.io.OutputStreamWriter");
//    allowPrefix.add("java.io.File.<init>");
//    allowPrefix.add("org.apache.");
//    allowPrefix.add("org.sat4j.");
//    allowPrefix.add("com.martiansoftware.");
//    allowPrefix.add("edu.uci.ics.crawler4j.");
      allowPrefix.add("org.");
//    allowPrefix.add("hk.ust.cse.Prevision_PseudoImpl.");
    extractor.produceAllMethodList(allowPrefix);
  }
  
  private final ForwardExecutor m_executor;
}
