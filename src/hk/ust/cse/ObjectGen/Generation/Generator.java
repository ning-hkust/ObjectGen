package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.ObjectGen.Generation.Generators.ArrayGenerator;
import hk.ust.cse.ObjectGen.Generation.Generators.AssignFieldGenerator;
import hk.ust.cse.ObjectGen.Generation.Generators.GenerationResult;
import hk.ust.cse.ObjectGen.Generation.Generators.ObjectGenerator;
import hk.ust.cse.ObjectGen.Generation.Generators.SimpleGenerator;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Instance.INSTANCE_OP;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Wala.SubClassHack;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;

public class Generator {

  public Generator(String appJar, 
                   String pseudoImplJarFile, 
                   String javaSummaryDBPath, 
                   String otherSummaryDBPath, 
                   HashSet<String> filterMethods, 
                   int maxStep, 
                   int maxSubClasses, 
                   int accessibility,  
                   boolean allowStaticNotSat) throws Exception {
    
    m_maxStep           = maxStep;
    m_maxSubClasses     = maxSubClasses;
    m_allowStaticNotSat = allowStaticNotSat;
    m_walaAnalyzer      = new WalaAnalyzer(appJar);
    m_satCache          = new SatisfiedReqCache();
    m_unsatCache        = new UnsatisfiedReqCache();

    if (pseudoImplJarFile != null) {
      m_walaAnalyzer.addJarFile(pseudoImplJarFile);
    }
    
    // load jar file, _removed.jar version is for faster call graph construction. Since it may 
    // be missing some classes (e.g. UnknownElement), we should use the full version in classloader
    appJar = appJar.endsWith("_removed.jar") ? appJar.substring(0, appJar.length() - 12) + ".jar" : appJar;
    Utils.loadJarFile(appJar);

    m_arrayGenerator       = new ArrayGenerator(this, accessibility);
    m_simpleGenerator      = new SimpleGenerator(this, accessibility);
    m_objectGenerator      = new ObjectGenerator(this, accessibility, maxStep, pseudoImplJarFile, javaSummaryDBPath, otherSummaryDBPath, filterMethods);
    m_assignFieldGenerator = new AssignFieldGenerator(this, accessibility);
  }
  
  public Sequence generate(Requirement req, VarNamePool varNamePool, Hashtable<Long, String> hashCodeVarMap) {
    m_stopFlag       = false;
    m_varNamePool    = varNamePool;
    m_hashCodeVarMap = hashCodeVarMap;
    List<Requirement> ancestorReqs = new ArrayList<Requirement>();
    ancestorReqs.add(req);
    return generate(req, ancestorReqs);
  }
  
  private Sequence generate(Requirement req, List<Requirement> ancestorReqs) {
    Sequence genSequence = null;
    
    try {
      // handle and remove information about pseudo implementation
      Long creating4Hash = null;
      Object handleResult = handleHashCodeHack(req);
      if (handleResult instanceof Sequence) {
        genSequence = (Sequence) handleResult;
      }
      else if (handleResult instanceof Long) {
        creating4Hash = (Long) handleResult;
      }
      
      // try simple generator first
      if (genSequence == null) {
        genSequence = m_simpleGenerator.generate(req, ancestorReqs);
      }

      // try array generator
      String typeName = req.getTargetInstance().getLastRefType();
      if (genSequence == null && typeName.startsWith("[")) {
        genSequence = m_arrayGenerator.generate(req, ancestorReqs);
      }

      // try object generator
      if (genSequence == null && !typeName.startsWith("[")) {
        // if it is an abstract class or interface, use concrete classes
        boolean useConcrete = false;
        if (m_maxSubClasses > 0) {
          Class<?> cls = Utils.findClass(typeName);
          if (cls != null && (Modifier.isAbstract(cls.getModifiers()) || cls.isInterface())) {
            List<String> subClasses = WalaUtils.getSubClasses(m_walaAnalyzer, typeName, true, false);
            subClasses = sortSubClasses(typeName, subClasses, m_maxSubClasses);
            for (int i = 0, size = subClasses.size(); i < size && i < m_maxSubClasses && genSequence == null; i++) {
              req.setTargetInstanceType(subClasses.get(i));
              genSequence = m_objectGenerator.generate(req, ancestorReqs);
              useConcrete = true;
            }
          }
        }

        if (!useConcrete) {
          genSequence = m_objectGenerator.generate(req, ancestorReqs);
        }
      }
      
      // in case all fields are accessible, try to directly set these fields
      if (genSequence == null && m_assignFieldGenerator.allFieldsAccessible(req)) {
        genSequence = m_assignFieldGenerator.generate(req, ancestorReqs);
      }
      
      // generation sequence of object of this hashcode
      if (creating4Hash != null && genSequence != null) {
        m_hashCodeVarMap.put(creating4Hash, genSequence.getKeyVariable().getVarName());
      }
    } catch (Exception e) {e.printStackTrace();}

    return genSequence;
  }

  public GenerationResult gen4ChildReqs(Requirements childReqs, List<Requirement> ancestorReqs) {
    GenerationResult genResult = new GenerationResult();
    
    // get or create a generating order
    List<String> ensureGenOrder = childReqs.getEnsureGenOrder();
    ensureGenOrder = ensureGenOrder == null ? Utils.enumerateToList(childReqs.keys()) : ensureGenOrder;
    
    // check if childReqs contains ancestor requirement
    for (int i = 0, size = ensureGenOrder.size(); i < size && !genResult.hasNotSat(); i++) {
      String varName = ensureGenOrder.get(i);
      if (!varName.startsWith("L")) {
        Requirement childReq = childReqs.getRequirement(varName);
        for (int j = 0, size2 = ancestorReqs.size(); j < size2 && !genResult.hasNotSat(); j++) {
          if (childReq.subsumes(ancestorReqs.get(j))) {
            genResult.addNotSat(varName);
          }
        }
      }
    }
    
    // check if any childReq is already known to be not satisfiable
    Enumeration<String> keys = childReqs.keys();
    while (keys.hasMoreElements() && !genResult.hasNotSat()) {
      String varName = (String) keys.nextElement();
      Requirement childReq = childReqs.getRequirement(varName);

      if (m_unsatCache.isAlreadyUnsat(childReq, ancestorReqs.size() + 1)) {
        genResult.addNotSat(varName);
      }
    }

    // try to generate sequence for each child requirement
    keys = childReqs.keys();
    while (keys.hasMoreElements() && !genResult.hasNotSat() && !getStopFlag()) {
      String varName = (String) keys.nextElement();
      Requirement childReq = childReqs.getRequirement(varName);
      
      // try to find a match from cache first
      Sequence sequence    = null;
      boolean seqFromCache = false;
      if (!childReq.hashCodeHackRelated()) { // could be not correct when hashCode hack is involved
        sequence = m_satCache.findSequence(childReq);
        if (sequence != null) {
          // use the same sequence but with different variable names
          sequence = sequence.cloneWithNewNames(m_varNamePool);
          seqFromCache = true;
        }
      }
      
      // recursively generate code
      if (sequence == null && ancestorReqs.size() < m_maxStep) {
        List<Requirement> nextAnacestors = new ArrayList<Requirement>(ancestorReqs);
        nextAnacestors.add(childReq);
        sequence = generate(childReq, nextAnacestors);
      }
      
      // cannot generate sequence for this requirement
      if (sequence == null && (!m_allowStaticNotSat || !varName.startsWith("L"))) {
        genResult.addNotSat(varName);
      }
      else if (sequence != null) {
        genResult.addSequence(varName, sequence);
      }

      // save the generated sequence, could be null representing cannot generate
      if (sequence != null && !seqFromCache) {
        m_satCache.saveSequence(childReq, sequence);
      }
      else if (sequence == null) {
        m_unsatCache.saveUnsatReq(childReq, ancestorReqs.size() + 1);
      }
    }
    
    return genResult;
  }
  
  // handle the __hashCode__ hack, remove any field that comes from the pseudo class
  // and replace the type name of the target instance when necessary. After this method, 
  // the requirement should become normal and does not relate the pseudo implementations
  private Object handleHashCodeHack(Requirement req) {
    Object ret = null;
    
    for (int i = 0; i < req.getConditions().size(); i++) {
      BinaryConditionTerm binaryTerm = req.getConditions().get(i).getOnlyBinaryTerm();
      if (binaryTerm == null) {
        continue;
      }
      
      Instance instance1 = binaryTerm.getInstance1();
      if (!instance1.isBounded() && instance1.getLastRefName().equals("__hashcode__")) { // v9999.__hashcode__ == #!0
        Instance declInstance = instance1.getLastReference().getDeclaringInstance();
        if (declInstance == req.getTargetInstance()) { // v9999.__hashCode__
          long modelValue = Long.parseLong(binaryTerm.getInstance2().getValueWithoutPrefix());
          if (modelValue < 0) {
            // if v9999.__hashCode__ < 0, that means we don't want to find any 
            // element from Map by key v9999. Thus, creating a new Object for v1 
            // (v1 != null) will work just find
            req.getConditions().remove(i--);
          }
          else {
            String varForThisValue = m_hashCodeVarMap.get(modelValue);
            if (varForThisValue != null) { // object for this hash code has been created already
              String typeName = "Ljava/lang/Object";
              Variable assignTo   = new Variable(m_varNamePool.nextVariableName(), typeName);
              Variable assignFrom = new Variable(varForThisValue, typeName);
              Sequence sequence = new Sequence(assignTo);
              sequence.addAssignStatement(assignTo, assignFrom);
              ret = sequence;
            }
            else { // remove the v9999.__hashcode__ == #!0 condition, mark down what hash code this object is for
              req.getConditions().remove(i--);
              ret = modelValue;
            }
          }
        }
        
        // we need to create an Object, not the pseudo class HashCode
        if (req.getTargetInstance().getLastRefType().equals("Lhk/ust/cse/Prevision_PseudoImpl/HashCode")) {
          req.setTargetInstanceType("Ljava/lang/Object");
        }
      }
    }
    
    // remove terms with "__table__" and Hashtable.size == 0 as 
    // the real object we try to create won't have these fields
    for (int i = 0; i < req.getConditions().size(); i++) {
      BinaryConditionTerm binaryTerm = req.getConditions().get(i).getOnlyBinaryTerm();
      if (binaryTerm == null) {
        continue;
      }
      
      Instance instance1 = binaryTerm.getInstance1();
      Instance instance2 = binaryTerm.getInstance2();
      
      // Hashtable does not have size field, the field is only used by the pseudo class
      if (instance1.getLastReference() != null && instance1.getLastRefName().equals("size") && 
          instance2.getValue() != null && instance2.getValue().equals("#!0")) {
        
        String typeName = instance1.getLastReference().getDeclaringInstance().getType();
        typeName = (typeName == null && instance1.getLastReference().getDeclaringInstance().getLastReference() != null) ? 
            instance1.getLastReference().getDeclaringInstance().getLastRefType() : typeName;
        if (typeName != null && typeName.contains("Hashtable")) {
          req.getConditions().remove(i--);
          continue;
        }
      }
      
      while (instance1 != null && instance1.getLastReference() != null) {
        if (instance1.getLastRefName().equals("__table__")) { // __table__ won't exist the real object type
          req.getConditions().remove(i--);
          break;
        }
        instance1 = instance1.getLastReference().getDeclaringInstance();
      }
    }
    
    // convert Prevision_PseudoImpl/HashCode type to Object type.
    // This is due to the bug that, solver may assign the value 
    // object (which is Object type) a model value within Prevision_PseudoImpl/HashCode.
    // Once we solve this solver bug, we can remove this part.
    if (req.getTargetInstance().getLastRefType().equals("Lhk/ust/cse/Prevision_PseudoImpl/HashCode")) {
      req.setTargetInstanceType("Ljava/lang/Object");
    }
    
    return ret;
  }
  

  

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
  
  public WalaAnalyzer getWalaAnalyzer() {
    return m_walaAnalyzer;
  }
  
  public boolean getStopFlag() {
    return m_stopFlag;
  }
  
  public VarNamePool getVarNamePool() {
    return m_varNamePool;
  }
  
  public Hashtable<Long, String> getHashCodeVarMap() {
    return m_hashCodeVarMap;
  }
  
  public void setStopFlag() {
    m_stopFlag = true;
  }
  
  public void setHashCodeVarMap(Hashtable<Long, String> hashCodeVarMap) {
    m_hashCodeVarMap = hashCodeVarMap;
  }
  
//  // obj.size == 3
//  public static void main(String[] args) throws Exception {
//    Reference target = new Reference("v9999", "Lhk/ust/cse/ObjectGen/TestCases/TestObjectGen", "", new Instance("", null), null, true);
//    Instance instance1 = new Instance("", null);
//    Instance instance2 = new Instance("#!3", "I", null);
//    target.getInstance().setField("size", "I", "", instance1, true, true);
//    BinaryConditionTerm term = new BinaryConditionTerm(instance1, Comparator.OP_EQUAL, instance2);
//    Requirement req = new Requirement();
//    req.addRequirementTerm(term);
//    req.setTargetInstance(target.getInstance());
//    
//    Generator generator = new Generator("./hk.ust.cse.ObjectGen.jar", "./summaries/", 10, 5);
//    Sequence sequence = generator.generate(req, new int[]{0});
//    if (sequence != null) {
//      System.out.println(sequence.toString());
//    }
//    else {
//      System.err.println("Failed to generate sequence!");
//    }
//  }
  
//  // obj.size == 3 where obj is type of AbstractTestObjectGen
//  public static void main(String[] args) throws Exception {
//    Reference target = new Reference("v9999", "Lhk/ust/cse/ObjectGen/TestCases/AbstractTestObjectGen", "", new Instance("", null), null, true);
//    Instance instance1 = new Instance("", null);
//    Instance instance2 = new Instance("#!3", "I", null);
//    target.getInstance().setField("size", "I", "", instance1, true, true);
//    BinaryConditionTerm term = new BinaryConditionTerm(instance1, Comparator.OP_EQUAL, instance2);
//    Requirement req = new Requirement();
//    req.addRequirementTerm(term);
//    req.setTargetInstance(target.getInstance());
//    
//    Generator generator = new Generator("./hk.ust.cse.ObjectGen.jar", "./summaries/", 10, 5, 1);
//    Sequence sequence = generator.generate(req, new int[]{0});
//    if (sequence != null) {
//      System.out.println(sequence.toString());
//    }
//    else {
//      System.err.println("Failed to generate sequence!");
//    }
//  }
  
  // obj.list.length == 2
  // obj.list != null
  // obj.list[1] != null
  public static void main(String[] args) throws Exception {
    Instance instanceNum2 = new Instance("#!2", "I", null);
    Instance instanceNull = new Instance("null", "", null);
    
    Reference target = new Reference("v9999", "Lhk/ust/cse/ObjectGen/TestCases/TestObjectGen", "", new Instance("", null), null, true);
    target.getInstance().setField("list", "[I", "", new Instance("", null), true, true);
    Reference fieldList = target.getInstance().getField("list");
    fieldList.getInstance().setField("length", "I", "", new Instance("", null), true, true);
    Reference fieldLen = fieldList.getInstance().getField("length");
    
    Instance left  = fieldList.getInstance();
    Instance right = new Instance("#!1", "I", null);
    Instance array = new Instance(left, INSTANCE_OP.DUMMY, right, null);
    
    BinaryConditionTerm term1 = new BinaryConditionTerm(fieldLen.getInstance(), Comparator.OP_EQUAL, instanceNum2);
    BinaryConditionTerm term2 = new BinaryConditionTerm(fieldList.getInstance(), Comparator.OP_INEQUAL, instanceNull);
    BinaryConditionTerm term3 = new BinaryConditionTerm(array, Comparator.OP_INEQUAL, instanceNull);
    Requirement req = new Requirement(target.getInstance().getLastRefName());
    req.addCondition(new Condition(term1));
    req.addCondition(new Condition(term2));
    req.addCondition(new Condition(term3));
    req.setTargetInstance(target.getInstance(), false);
    
    Generator generator = new Generator("./hk.ust.cse.ObjectGen.jar", "./java_summaries/", "./summaries/", 
        "./lib/hk.ust.cse.Prevision_PseudoImpl.jar", new HashSet<String>(), 5, 1, 1, true);
    Sequence sequence = generator.generate(req, new VarNamePool(), new Hashtable<Long, String>());
    if (sequence != null) {
      System.out.println(sequence.toString());
    }
    else {
      System.err.println("Failed to generate sequence!");
    }
  }
  
  private boolean                    m_stopFlag;
  private VarNamePool                m_varNamePool;
  private Hashtable<Long, String>    m_hashCodeVarMap;
  private final int                  m_maxStep;
  private final int                  m_maxSubClasses;
  private final boolean              m_allowStaticNotSat;
  private final WalaAnalyzer         m_walaAnalyzer;
  private final SatisfiedReqCache    m_satCache;
  private final UnsatisfiedReqCache  m_unsatCache;

  private final ArrayGenerator       m_arrayGenerator;
  private final SimpleGenerator      m_simpleGenerator;
  private final ObjectGenerator      m_objectGenerator;
  private final AssignFieldGenerator m_assignFieldGenerator;
}
