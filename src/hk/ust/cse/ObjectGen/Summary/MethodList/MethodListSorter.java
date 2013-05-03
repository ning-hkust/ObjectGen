package hk.ust.cse.ObjectGen.Summary.MethodList;

import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.ObjectGen.Summary.SummaryDatabase;
import hk.ust.cse.Prevision.InstructionHandlers.CompleteForwardHandler;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.Solver.SMTChecker.SOLVERS;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision.VirtualMachine.Executor.ForwardExecutor;
import hk.ust.cse.Wala.SubClassHack;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

public class MethodListSorter {

  public MethodListSorter(String appJar, String pseudoImplJar) throws Exception {
    m_forwardExecutor      = new ForwardExecutor(appJar, pseudoImplJar, new CompleteForwardHandler(), new SMTChecker(SOLVERS.Z3));
    m_intraSummaryDatabase = new SummaryDatabase("./java_intra_summaries/", "./intra_summaries/", 20, m_forwardExecutor.getWalaAnalyzer());
  }
  
  // a up-front all_methods.txt and intra-summaries should have already been prepared
  public void produceAllMethodSortedList(String allMethodsFile, String allMethodsSortedFile) {
    // read all methods
    List<String> allMethodsList   = new ArrayList<String>();
    HashSet<String> allMethodsSet = new HashSet<String>();
    try {
      BufferedReader reader = new BufferedReader(new FileReader(allMethodsFile));
      String line1 = null;
      while ((line1 = reader.readLine()) != null) {
        allMethodsList.add(line1);
        allMethodsSet.add(line1);
      }
      reader.close();
    } catch (IOException e) {}
    
    // sort and write all sorted methods
    List<String> sortedList = sort(allMethodsList, allMethodsSet);
    try {
      BufferedWriter writer = new BufferedWriter(new FileWriter(allMethodsSortedFile));
      for (String methodSig : sortedList) {
        writer.append(methodSig).append("\n");
      }
      writer.close();
    } catch (IOException e) {}
  }
  
  private List<String> sort(List<String> allMethodsList, HashSet<String> allMethodsSet) {
    // sort each method
    List<String> sortedList = new ArrayList<String>();
    HashSet<String> sortedSet = new HashSet<String>();
    
    int index = 1;
    for (String methodSig : allMethodsList) {
      System.out.println("(" + (index++) + " / " + allMethodsList.size() + ") Sorting: " + methodSig);
      sortMethod(methodSig, new ArrayList<String>(), allMethodsSet, sortedSet, sortedList);
    }
    
    return sortedList;
  }
  
  private void sortMethod(String methodSig, List<String> prevMethods, HashSet<String> allMethodsSet, 
      HashSet<String> sortedSet, List<String> sortedList) {
    
    if (sortedSet.contains(methodSig) || !allMethodsSet.contains(methodSig) || prevMethods.contains(methodSig)) {
      return;
    }
    
    // read intra-summaries
    prevMethods.add(methodSig);
    List<Summary> intraSummaries = m_intraSummaryDatabase.readSummaries(methodSig);
    if (intraSummaries != null) {
      for (Summary intraSummary : intraSummaries) {
        List<String> invocationSigs = new ArrayList<String>();
        
        // find all invocation methods
        Collection<Reference> invocations = intraSummary.findAllInvocations();
        for (Reference invocation : invocations) {
          int index1 = invocation.getName().lastIndexOf('_');
          String invocationSig = invocation.getName().substring(0, index1);
          invocationSigs.add(invocationSig);
        }
        
        for (String invocationSig : invocationSigs) {
          sortMethod(invocationSig, prevMethods, allMethodsSet, sortedSet, sortedList);
        }
      }
    }
    else { // this part should be the same as in summary computation
      int index         = methodSig.lastIndexOf('.');
      String declClass  = methodSig.substring(0, index);
      String methodName = methodSig.substring(index);

      // try the invocation in sub-classes
      List<String> subMethodSigs = new ArrayList<String>();
      List<String> subClasses = WalaUtils.getSubClasses(m_forwardExecutor.getWalaAnalyzer(), declClass, true, false);
      subClasses = sortSubClasses(declClass, subClasses, subClasses.size());
      for (int i = 0, size = subClasses.size(); i < size && subMethodSigs.size() < 2 /* max sub-classes use */; i++) {
        String subMethodSig = Utils.getClassTypeJavaStr(subClasses.get(i), false) + methodName;
        
        // only extract sub-methods that are in the allMethodSet
        if (allMethodsSet.contains(subMethodSig)) {
          subMethodSigs.add(subMethodSig);
        }
      }
      
      for (String subMethodSig : subMethodSigs) {
        sortMethod(subMethodSig, prevMethods, allMethodsSet, sortedSet, sortedList);
      }
    }
    prevMethods.remove(prevMethods.size() - 1);
    
    sortedSet.add(methodSig);
    sortedList.add(methodSig);
  }

  // should be an exact copy from SummaryExtractor
  private List<String> sortSubClasses(String superClass, List<String> subClasses, int maxSubClasses) {
    List<String> sorted = new ArrayList<String>();
    
    // use the frequent ones first
    List<String> freqList = SubClassHack.useFreqSubclasses(superClass);
    if (freqList != null) {
      sorted.addAll(freqList);
    }
    else {
      // find those with simple constructor
      for (int i = 0, size = subClasses.size(); i < size && sorted.size() < maxSubClasses; i++) {
        Class<?> cls = Utils.findClass(subClasses.get(i));
        if (cls != null) {
          boolean easy = false;
          Constructor<?>[] ctors = Utils.getPublicCtors(cls);
          for (int j = 0; j < ctors.length && !easy; j++) {
            easy = ctors[j].getParameterTypes().length == 0;
          }
          if (easy) {
            sorted.add(subClasses.get(i));
          }
        }
      }
      
      // fill the rest
      for (int i = 0, size = subClasses.size(); i < size && sorted.size() < maxSubClasses; i++) {
        if (!sorted.contains(subClasses.get(i))) {
          sorted.add(subClasses.get(i));
        }
      }
    }

    return sorted;
  }
  
  public static void main(String[] args) throws Exception {
    MethodListSorter sorter = new MethodListSorter(args[0] /* jar file */, args[1] /* pseudoImplJar */);
    sorter.produceAllMethodSortedList(args[2] /* all methods file */, args[3] /* output sorted method file */);
  }
  
  private final ForwardExecutor m_forwardExecutor;
  private final SummaryDatabase m_intraSummaryDatabase;
}
