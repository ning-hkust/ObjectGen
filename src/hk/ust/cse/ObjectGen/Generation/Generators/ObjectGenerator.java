package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Requirements;
import hk.ust.cse.ObjectGen.Generation.Generators.ParamReqDeductor.DeductResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.ObjectGen.Selection.AbstractMethodSelector;
import hk.ust.cse.ObjectGen.Selection.AbstractSummarySelector;
import hk.ust.cse.ObjectGen.Selection.FieldMethodSelector;
import hk.ust.cse.ObjectGen.Selection.SimpleSummarySelector;
import hk.ust.cse.ObjectGen.Selection.TreeSummarySelector;
import hk.ust.cse.ObjectGen.Summary.Summary;
import hk.ust.cse.ObjectGen.Summary.SummaryDatabase;
import hk.ust.cse.Prevision.Solver.SMTChecker;
import hk.ust.cse.Prevision.Solver.SMTChecker.SOLVERS;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Constructor;
import java.lang.reflect.Member;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class ObjectGenerator extends AbstractGenerator {

  public ObjectGenerator(Generator allTypeGenerator, int accessibility, int maxStep, int[] findMoreValues, 
      String pseudoImplJarFile, String summaryDBPath, HashSet<String> filterMethods) {
    super(allTypeGenerator, accessibility);

    m_maxStep         = maxStep;
    m_findMoreValues  = findMoreValues;
    m_filterMethods   = filterMethods;
    m_smtChecker      = new SMTChecker(SOLVERS.Z3);
    //m_selector      = new SimpleMethodSelector(m_maxSelect);
    m_selector        = new FieldMethodSelector(m_walaAnalyzer, pseudoImplJarFile != null, accessibility);
    m_summaryDatabase = new SummaryDatabase(summaryDBPath, 20, m_walaAnalyzer);
  }

  @Override
  @SuppressWarnings("unchecked")
  public Sequence generate(Requirement req, List<Requirement> ancestorReqs) {
    Variable targetAssignFrom  = null;
    IR selectedIR              = null;
    GenerationResult genResult = null;
    
    // check if requirement can be set directly
    Sequence genSequence = trySetDirectly(req);
    
    // if not, generate this object
    if (genSequence == null) {
      HashSet<String> factoryOrCreateInners = new HashSet<String>();
      List<String> potentialMethods = new ArrayList<String>();

      // for inner class or inner anonymous class, find creation methods from outer class
      Class<?> targetType = req.getTargetType();
      List<String> createInnerMethods = null;
      if (!Modifier.isPublic(targetType.getModifiers()) && targetType.isMemberClass()) {
        Class<?> outerClass = targetType.getDeclaringClass();
        createInnerMethods = findCreateInnerMethods(outerClass, targetType);
      }
      else if (Utils.isAnonymousClass(targetType)) {
        String clsName = targetType.getName();
        Class<?> outerClass = Utils.findClass(clsName.substring(0, clsName.lastIndexOf('$')));
        createInnerMethods = findCreateInnerMethods(outerClass, targetType);
      }
      if (createInnerMethods != null) {
        factoryOrCreateInners.addAll(createInnerMethods);
        potentialMethods.addAll(createInnerMethods);
      }
      
      // if we only need to satisfy v1 != null or we are at the maxStep step, 
      // only allow constructor or factoryOrCreateInners methods
      boolean onlyVarNotNullReq = onlyVarNotNullReq(req);
      if (onlyVarNotNullReq || ancestorReqs.size() == m_maxStep) {
        // get constructor methods
        potentialMethods.addAll(findInitMethods(req));
        List<String> factoryMethods = findFactoryMethods(req);
        factoryOrCreateInners.addAll(factoryMethods);
        potentialMethods.addAll(factoryMethods);
        sortInitsByDifficulty(potentialMethods);
      }
      else {
        // select potential methods
        potentialMethods.addAll(m_selector.select(req)); 
        List<String> factoryMethods = findFactoryMethods(req);
        factoryOrCreateInners.addAll(factoryMethods);
        potentialMethods.addAll(factoryMethods);
        sortBySummaryCount(potentialMethods);
        sortByPreferences(potentialMethods, factoryOrCreateInners);
      }
      
      // remove any potential redundancy
      potentialMethods = (List<String>) Utils.deleteRedundents(potentialMethods);
      
      // if only v9999 != null left, and we see a simple constructor, just use it!
      IR directCreate = null;
      for (int i = 0, size = potentialMethods.size(); i < size && onlyVarNotNullReq && directCreate == null; i++) {
        // if we only try to set v1 != null, and we see a direct constructor, just use it!
        if (potentialMethods.get(i).endsWith(".<init>()V")) {
          Variable keyVariable = new Variable(nextVariableName(), req.getTargetInstance().getLastRefType());
          genResult = new GenerationResult();
          genResult.addSequence("v1", new Sequence(keyVariable));
          
          targetAssignFrom = keyVariable;
          directCreate = Jar2IR.getIR(m_walaAnalyzer, potentialMethods.get(i));
        }
      }
      
      // try each potential methods sequentially
      boolean targetFromRet = false;
      for (int i = 0, size = potentialMethods.size(); 
          i < size && selectedIR == null && directCreate == null && !m_allTypeGenerator.getStopFlag(); i++) {

        String potentialMethodSig = potentialMethods.get(i);
        if (m_filterMethods.contains(potentialMethodSig)) {
          System.out.println("Filtered method: " + potentialMethodSig);
          continue;
        }
        
        // output current status
        printStepSpaces(ancestorReqs.size());
        System.out.println(" trying " + potentialMethodSig + " at step " + (ancestorReqs.size()));
        
        // identify if current method is factory or create inner class method
        boolean isFactoryOrCreateInner = factoryOrCreateInners.contains(potentialMethodSig);
        
        // obtain fully expanded summaries for this method
        List<Summary> methodSummaries = m_summaryDatabase.readSummaries(potentialMethodSig);
        if (methodSummaries == null || methodSummaries.size() == 0) {
          // for performance reason,  we do not compute summaries on the fly
          System.out.println("Failed to find or extract any summary for the method!");
          continue;
        }
        
        // do not use the one in summary, due to pseudo implementation
        IR ir = Jar2IR.getIR(m_walaAnalyzer, potentialMethodSig);
        Class<?> irDeclType = Utils.findClass(ir.getMethod().getDeclaringClass().getName().toString());
        
        // cannot invoke the constructor of a private or anonymous class, even if the constructor is public
        boolean isInitMethod = ir.getMethod().isInit();
        if (isInitMethod && (irDeclType == null || 
                             Modifier.isPrivate(irDeclType.getModifiers()) || 
                             Utils.isAnonymousClass(irDeclType))) {
          continue;
        }
        
        // create summary selector
        AbstractSummarySelector summarySelector = methodSummaries.size() > 10000 ? 
            new TreeSummarySelector(methodSummaries, req, ir, isFactoryOrCreateInner, this) : 
            new SimpleSummarySelector(methodSummaries, req, ir, this); 
        System.out.println("Original Summary Count: " + methodSummaries.size() + 
            ". Refined Summary Count: " + summarySelector.getSummaryCount());
        
        int summaryIndex               = 0;
        Requirements prevChildReqs     = null;
        GenerationResult prevGenResult = null;
        ParamReqDeductor deductor = new ParamReqDeductor(ir, isFactoryOrCreateInner, this);
        while (summarySelector.hasNext() && selectedIR == null && !m_allTypeGenerator.getStopFlag()) {
          summaryIndex++;
          
          // retrieve next summary according to previous generation result
          List<Requirement> prevSatReqs  = new ArrayList<Requirement>();
          if (prevChildReqs != null && prevGenResult != null) {
            for (String varName : prevGenResult.getGenOrder()) {
              prevSatReqs.add(prevChildReqs.getRequirement(varName));
            }
          }
          Summary summary = summarySelector.nextSummary(prevSatReqs);
          
          Hashtable<Long, String> prevHashCodeVarMap = 
              (Hashtable<Long, String>) m_allTypeGenerator.getHashCodeVarMap().clone();
          
          try {
            DeductResult deductResult = summarySelector.getDeductResult(summary);
            deductResult = deductResult == null ? deductor.deductChildReqs(summary, req) : deductResult;
            if (deductResult == null) {
              continue; // try next summary
            }
            targetAssignFrom = deductResult.keyVariable;
            targetFromRet    = deductResult.returnValIsKey;
            
            printStepSpaces(ancestorReqs.size());
            System.out.println(" the " + summaryIndex + "th summary can be further deducted...");
            
            // ensure generating order if possible
            List<String> ensureOrder = Utils.enumerateToList(deductResult.childReqs.keys());
            ensureOrder = summarySelector.createEnsureGenOrder(ensureOrder);
            deductResult.childReqs.setEnsureGenOrder(ensureOrder);
            
            // generate recursively for the child requirements
            genResult = m_allTypeGenerator.gen4ChildReqs(deductResult.childReqs, ancestorReqs);
            
            // inform selector about generation results
            for (String varName : genResult.getGenOrder()) {
              Sequence seq = genResult.getSequence(varName);
              summarySelector.informChildReqSat(deductResult.childReqs.getRequirement(varName), seq);
            }
            for (String varName : genResult.getNotSatVarNames()) {
              summarySelector.informChildReqNotSat(deductResult.childReqs.getRequirement(varName));
            }
            prevChildReqs = deductResult.childReqs;
            prevGenResult = genResult;
            
            // generated
            if (!genResult.hasNotSat()) {
              if (!targetFromRet && targetAssignFrom != null) {
                for (String varName : genResult.getGenOrder()) {
                  // currently, varName is the actual parameter pos, v1, v2
                  // assign to targetAssignFrom with the actual variable name
                  if (targetAssignFrom.getVarName().equals(varName)) {
                    targetAssignFrom = genResult.getSequence(varName).getKeyVariable();
                  }
                }
              }
              selectedIR = ir; // select this method

              // put empty sequence for v1
              if (isInitMethod && deductResult.canEndByCtor) {
                Variable keyVariable = new Variable(nextVariableName(), req.getTargetInstance().getLastRefType());
                genResult.addSequence("v1", new Sequence(keyVariable));
                targetAssignFrom = keyVariable;
              }
            }
            else {
              m_allTypeGenerator.setHashCodeVarMap(prevHashCodeVarMap);
            }
          } catch (Throwable e) {
            m_allTypeGenerator.setHashCodeVarMap(prevHashCodeVarMap);
            e.printStackTrace();
            continue;
          }
        }
      }
      
      // add the selected method to sequence
      if (directCreate != null || (selectedIR != null && !genResult.hasNotSat())) {
        genSequence = new Sequence(targetAssignFrom);
        
        Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
        for (String varName : genResult.getGenOrder()) {
          Sequence sequence = genResult.getSequence(varName);
          parameters.put(varName, sequence.getKeyVariable());
          genSequence.mergeSequence(sequence);
        }
        
        // check if we need to create an inner class to invoke this method
        IR ir = directCreate != null ? directCreate : selectedIR;
        Class<?> irDeclType = Utils.findClass(ir.getMethod().getDeclaringClass().getName().toString());
        boolean v1UsesInnerClass = req.getUseInnerClass() || (!targetFromRet && 
                                   ((!ir.getMethod().isStatic() && ir.getMethod().isProtected()) || 
                                   ((Modifier.isProtected(irDeclType.getModifiers()) || 
                                     Modifier.isAbstract(irDeclType.getModifiers())) && ir.getMethod().isInit())));
        genSequence.addMethod(ir, parameters, v1UsesInnerClass);
      }
    }
    
    return genSequence;
  }

  private static HashSet<String> s_easyList;
  private void sortInitsByDifficulty(List<String> inits) {
    if (s_easyList == null) {
      s_easyList = new HashSet<String>();
      s_easyList.add("Ljava/lang/Object");
      s_easyList.add("Ljava/lang/String");
    }
    
    final Hashtable<String, Integer> difficultyScores = new Hashtable<String, Integer>();
    for (String methodSig : inits) {
      int index1 = methodSig.indexOf('(');
      int index2 = methodSig.lastIndexOf(')');
      String params = methodSig.substring(index1 + 1, index2);
      String[] paramList = params.split(";");

      int score = 0;
      for (String param : paramList) {
        if (param.startsWith("L")) {
          if (!s_easyList.contains(param)) {
            score += 10000;
          }
          else {
            score += 100;
          }
        }
      }
      difficultyScores.put(methodSig, score);
    }
    
    Collections.sort(inits, new java.util.Comparator<String>() {
      @Override
      public int compare(String o1, String o2) {
        return difficultyScores.get(o1) - difficultyScores.get(o2);
      }
    });
  }
  
  private List<String> findInitMethods(Requirement req) {
    List<String> methodSigs = new ArrayList<String>();

    Class<?> cls = Utils.findClass(req.getTargetInstance().getLastRefType());
    if (cls != null) {
      Constructor<?>[] ctors = null;
      if (m_accessibility == 0) {
        ctors = Utils.getPublicCtors(cls);
      }
      else {
        ctors = Utils.getNonPrivateCtors(cls);
      }
      
      // output the method signatures
      for (Member ctor : ctors) {
        IR ir = Jar2IR.getIR(m_walaAnalyzer, ctor);
        if (ir != null && !initContainsAnonymousParam((Constructor<?>) ctor)) {
          methodSigs.add(ir.getMethod().getSignature());
        }
      }
    }

    return methodSigs;
  }
  
  // e.g.: org.apache.commons.collections.functors.PrototypeFactory$PrototypeCloneFactory(java.lang.Object,java.lang.reflect.Method,org.apache.commons.collections.functors.PrototypeFactory$1)
  private boolean initContainsAnonymousParam(Constructor<?> ctor) {
    boolean anonymous = false;
    Class<?>[] paramTypes = ctor.getParameterTypes();
    for (int i = 0; i < paramTypes.length && !anonymous; i++) {
      anonymous = Utils.isAnonymousClass(paramTypes[i]);
    }
    return anonymous;
  }
  
  private List<String> findFactoryMethods(Requirement req) {
    List<String> methodSigs = new ArrayList<String>();

    String typeName = req.getTargetInstance().getLastRefType();
    Class<?> cls = Utils.findClass(typeName);
    if (cls != null) {
      Method[] methods = Utils.getPublicMethods(cls);
      
      // output the method signatures
      for (Method method : methods) { // e.g., public static Transformer getInstance()
        int modifiers = method.getModifiers();
        if (Modifier.isPublic(modifiers) && Modifier.isStatic(modifiers) && !Modifier.isNative(modifiers)) {
          Class<?> returnClass = method.getReturnType();
          
          if (returnClass != null && returnClass != java.lang.Object.class && Utils.isSubClass(returnClass, cls)) {
            IR ir = Jar2IR.getIR(m_walaAnalyzer, method);
            if (ir != null) {
              methodSigs.add(ir.getMethod().getSignature());
            }
          }
        }
      }
    }

    return methodSigs;
  }
  
  private List<String> findCreateInnerMethods(Class<?> outerClass, Class<?> innerClass) {
    List<String> methodSigs = new ArrayList<String>();

    if (outerClass != null && innerClass != null) {
      Method[] methods = Utils.getPublicMethods(outerClass);
      
      // output the method signatures
      for (Method method : methods) { // e.g., public static Transformer getInstance()
        int modifiers = method.getModifiers();
        if (Modifier.isPublic(modifiers) && !Modifier.isNative(modifiers)) {
          Class<?> returnClass = method.getReturnType();
          
          if (returnClass != null && returnClass != java.lang.Object.class && Utils.isSubClass(returnClass, innerClass)) {
            IR ir = Jar2IR.getIR(m_walaAnalyzer, method);
            if (ir != null) {
              methodSigs.add(ir.getMethod().getSignature());
            }
          }
        }
      }
    }

    return methodSigs;
  }
  
  private void sortBySummaryCount(List<String> potentialMethods) {
    final Hashtable<String, Integer> countMap = new Hashtable<String, Integer>();
    for (String method : potentialMethods) {
      int count = m_summaryDatabase.readSummaryCount(method);
      countMap.put(method, count);
    }
    
    Collections.sort(potentialMethods, new java.util.Comparator<String>() {
      @Override
      public int compare(String method0, String method1) {
        int count0 = countMap.get(method0);
        int count1 = countMap.get(method1);
        return count0 - count1;
      }
    });
  }
  
  private void sortByPreferences(List<String> potentialMethods, HashSet<String> factoryOrCreateInners) {
    
    final Hashtable<String, Integer> preferScores = new Hashtable<String, Integer>();
    for (String method : potentialMethods) {
      int score = 0;
      
      // prefer by type
      IR ir = Jar2IR.getIR(m_walaAnalyzer, method);
      if (ir != null) {
        if (ir.getMethod().isInit()) {
          if (ir.getNumberOfParameters() == 1) {
            score += 1000;
          }
          else {
            score += 500;
          }
        }
        else if (factoryOrCreateInners.contains(method)) {
          score += 500;
        }
        else if (!ir.getMethod().isPublic()) {
          score -= 100;
        }
      }
    
      // prefer by name
      if (method.contains("add") || method.contains("init") || 
          method.contains("put") || method.contains("set")) {
        score += 200;
      }
      else if (method.contains("remove") || method.contains("clear") || 
               method.contains("reset")) {
        score -= 200;
      }
      preferScores.put(method, score);
    }

    Collections.sort(potentialMethods, new Comparator<String>() {
      @Override
      public int compare(String o1, String o2) {
        return preferScores.get(o2) - preferScores.get(o1);
      }
    });
  }
  
  private void printStepSpaces(int step) {
    for (int j = 0; j < step; j++) {
      System.out.print(">>");
    }
  }
  
  public SMTChecker getSMTChecker() {
    return m_smtChecker;
  }
  
  public int[] getFindMoreValues() {
    return m_findMoreValues;
  }
  
  private final int                    m_maxStep;
  private final int[]                  m_findMoreValues;
  private final HashSet<String>        m_filterMethods;
  private final SMTChecker             m_smtChecker;
  private final AbstractMethodSelector m_selector;
  private final SummaryDatabase        m_summaryDatabase;
}
