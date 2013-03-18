package hk.ust.cse.ObjectGen.IntraSummary;

import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.ObjectGen.Summary.SummaryDatabase;
import hk.ust.cse.Prevision.InstructionHandlers.CompleteForwardHandler;
import hk.ust.cse.Prevision.Misc.CallStack;
import hk.ust.cse.Prevision.Misc.InvalidStackTraceException;
import hk.ust.cse.Prevision.PathCondition.Formula;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.Solver.SMTChecker.SOLVERS;
import hk.ust.cse.Prevision.VirtualMachine.ExecutionOptions;
import hk.ust.cse.Prevision.VirtualMachine.Executor.ForwardExecutor;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.Utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.naming.TimeLimitExceededException;

import com.ibm.wala.ssa.IR;

public class IntraSummaryExtractor {

  public IntraSummaryExtractor(String appJar, String pseudoImplJar) throws Exception {
    m_executor = new ForwardExecutor(appJar, pseudoImplJar, new CompleteForwardHandler(), new SMTChecker(SOLVERS.YICES));
    m_intraSummaryDatabase = new SummaryDatabase("./intra_summaries/", 20, m_executor.getWalaAnalyzer());
    
    // load jar file, _removed.jar version is for faster call graph construction. Since it may 
    // be missing some classes (e.g. UnknownElement), we should use the full version in classloader
    appJar = appJar.endsWith("_removed.jar") ? appJar.substring(0, appJar.length() - 12) + ".jar" : appJar;
    Utils.loadJarFile(appJar);
  }
  
  public List<Summary> extract(String methodSig, boolean saveSummaries, long maxExtractTime) {

    try {
      // obtain initial intra-summaries of the method
      // read stack frames
      CallStack callStack = new CallStack(true);
      callStack.addStackTrace(methodSig, -1);
      
      // set options
      ExecutionOptions execOptions = new ExecutionOptions(callStack);
      execOptions.maxDispatchTargets    = 5;
      execOptions.maxRetrieve           = 100;
      execOptions.maxSmtCheck           = 1000;
      execOptions.maxInvokeDepth        = 0; // use expand instead of step in
      execOptions.maxLoop               = 1;
      execOptions.maxTimeAllow          = maxExtractTime;
      execOptions.clearSatNonSolverData = false;
      execOptions.addIRAsEntryPoint     = true;
      m_executor.compute(execOptions, null);
      
      // obtain all intra-summaries
      List<Summary> intraSummaries = new ArrayList<Summary>();
      for (Formula satisfiable : m_executor.getSatisfiables()) {
        Summary summary = new Summary(satisfiable, m_executor.getMethodMetaData());
        intraSummaries.add(summary);
      }
      
      // save to intra-summary database
      m_intraSummaryDatabase.saveSummariesOverride(methodSig, intraSummaries);
      
      return intraSummaries;

    } catch (InvalidStackTraceException e) {
      //System.err.println("Failed to locate method: " + methodSig); // compute() already printed exception msg
      return null;
    } catch (TimeLimitExceededException e) {
      System.err.println("Time limit exceeded when computing method: " + methodSig);
      return null;
    } catch (Exception e) {
      e.printStackTrace();
      return null;
    }
  }
  
  @SuppressWarnings("deprecation")
  public void extractAllMethods(long maxExtractTime, String methodListFile) throws Exception {
    long start = System.currentTimeMillis();

    // get the list of methods to extract
    List<String> methodsToExtract = new ArrayList<String>();
    List<String> extractedList    = new ArrayList<String>();
    List<String> failedList       = new ArrayList<String>();
    
    // read the last completed method
    try {
      BufferedReader reader = new BufferedReader(new FileReader(methodListFile));
      String line1 = null;
      while ((line1 = reader.readLine()) != null) {
        methodsToExtract.add(line1);
      }
      reader.close();
    } catch (IOException e) {}
    System.out.println(methodsToExtract.size() + " methods to extract intra-summaries...");

    // extract all methods
    BufferedWriter writer0 = new BufferedWriter(new FileWriter("./intra_summaries/summary_progress.txt", false));
    BufferedWriter writer1 = new BufferedWriter(new FileWriter("./intra_summaries/extracted_methods.txt", false));
    BufferedWriter writer2 = new BufferedWriter(new FileWriter("./intra_summaries/faileded_methods.txt", false));
    for (int i = 0, size = methodsToExtract.size(); i < size; i++) {
      String methodSig = methodsToExtract.get(i);
      
      System.out.println("Method (" + (i + 1) + " / " + size + "): " + methodSig);
      writer0.append(String.valueOf((i + 1))).append(": ").append(methodSig).append("...").flush();
      
      long start2 = System.currentTimeMillis();
      IntraSummaryExtractionThread thread = new IntraSummaryExtractionThread(this, methodSig, maxExtractTime);
      thread.start();
      
      long maxExtractTime2 = (long) (maxExtractTime * 1.1);
      while (thread.isAlive() && (System.currentTimeMillis() - start2) < maxExtractTime2) {
        Thread.sleep(25);
      }
      
      // stop long run methods
      boolean isLongRun = thread.isAlive();
      if (isLongRun) {
        thread.stop();
      }
      
      List<Summary> intraSummaries = thread.getIntraSummaries();
      if (intraSummaries != null) {
        extractedList.add(methodSig);
        writer1.append(methodSig + "\n").flush();
      }
      else {
        failedList.add(methodSig);
        writer2.append(methodSig + "\n").flush();
      }
      
      // save progress
      writer0.append(intraSummaries != null ? "Extracted!" : "Failed!").append(" (")
             .append(String.valueOf(extractedList.size())).append(" / ")
             .append(String.valueOf(failedList.size())).append(")")
             .append(" Total elapsed: ").append(String.valueOf(System.currentTimeMillis() - start2)).append(" ms\n").flush();
    }
    
    String endMsg = "Total elapsed: " + ((System.currentTimeMillis() - start) / 1000) + "s!";
    System.out.println(endMsg);
    writer0.append(endMsg + "\n").flush();
    
    writer0.close();
    writer1.close();
    writer2.close();
  }
  
  public ForwardExecutor getExecutor() {
    return m_executor;
  }
  
  public WalaAnalyzer getWalaAnalyzer() {
    return m_executor.getWalaAnalyzer();
  }
  
  public SummaryDatabase getIntraSummaryDatabase() {
    return m_intraSummaryDatabase;
  }
  
  // extract intra-summary methods
  public static void main(String args[]) throws Exception {
    if (args.length == 0) {
      //String appJar = "D:/Projects/BranchModelGenerator/targets/apache-commons-collections/target/commons-collections-3.2.1.jar";
      //String appJar = "D:/Projects/BranchModelGenerator/targets/sat4j/target/org.sat4j.core-2.2.0.jar";
      //String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-log4j/targets/log4j-1.2.15_removed.jar";
      //String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-ant/targets/ant-all-1.7.0_removed.jar";
      String appJar = "D:/Projects/STAR/experiments/ObjectGen/apache-commons-collections/targets/commons-collections-3.1.jar";
      //String appJar = "D:/Projects/ObjectGen/hk.ust.cse.ObjectGen.jar";
      String pseudoImplJar = "./lib/hk.ust.cse.Prevision_PseudoImpl.jar"; 
      IntraSummaryExtractor extractor = new IntraSummaryExtractor(appJar, pseudoImplJar);

      IR ir = Jar2IR.getIR(extractor.getWalaAnalyzer(), "org.apache.commons.collections.list.TreeList$AVLNode.insertOnRight(ILjava/lang/Object;)Lorg/apache/commons/collections/list/TreeList$AVLNode;");

      String methodSig = ir.getMethod().getSignature();
      List<Summary> intraSummaries = extractor.extract(methodSig, true, 100000);
      
      if (intraSummaries != null) {
        // display summaries
        for (int i = 0, size = intraSummaries.size(); i < size; i++) {
          System.out.println("Summary " + (i + 1) + ": =================================");
          System.out.println(intraSummaries.get(i));
          System.out.println();
        }
      }
    }
    else {
      IntraSummaryExtractor extractor = new IntraSummaryExtractor(args[0], args[1]);
      extractor.extractAllMethods(Integer.parseInt(args[2]), args[3]);
    }
  }
  
  private final ForwardExecutor m_executor;
  private final SummaryDatabase m_intraSummaryDatabase;
}
