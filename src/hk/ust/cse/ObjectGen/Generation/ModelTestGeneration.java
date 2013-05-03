package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.ObjectGen.Generation.Generators.GenerationResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.AssignmentStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.InvocationStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.JunitFileWriter;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Statement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Prevision.Misc.CallStack;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;
import hk.ust.cse.util.DbHelper.DbHelperSqlite;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.sql.Connection;
import java.sql.ResultSet;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ssa.IR;

public class ModelTestGeneration {
  
  public ModelTestGeneration(String appJar, String pseudoImplJarFile, String javaSummaryDBPath, 
      String otherSummaryDBPath, String modelDB, String outputDir, String filterModelsFile, String filterMethodsFile, 
      int maxStep, int maxSubClasses, int accessibility, boolean allowStaticNotSat) throws Exception {
    
    Utils.loadJarFile(appJar);
    
    HashSet<String> filterMethods = readFilterMethods(filterMethodsFile);
    m_generator = new Generator(appJar, pseudoImplJarFile, javaSummaryDBPath, 
        otherSummaryDBPath, filterMethods, maxStep, maxSubClasses, accessibility, allowStaticNotSat);
    m_junitFileWriter = new JunitFileWriter(outputDir);
    
    m_filterModelIDs = readFilterModelIDs(filterModelsFile);
    m_allowStaticNotSat = allowStaticNotSat;
    
    // model database name and table name
    m_dbName    = modelDB;
    m_tableName = "Model";
  }
  
  /**
   * @param modelID: one based
   */
  public void genTestCase(int modelID, long maxTimeAllow, boolean allowRelaxGen) {
    genTestCases(modelID, modelID + 1, maxTimeAllow, allowRelaxGen, false);
  }
  
  /**
   * @param fromModelID: one based
   * @param toModelID: one based
   * @param allowRelaxGen: use a simple callee when the precise callee cannot be generated
   */
  public void genTestCases(int fromModelID, int toModelID, long maxTimeAllow, boolean allowRelaxGen, boolean logStatus) {
    Connection conn = null;
    try {
      conn = DbHelperSqlite.openConnection(m_dbName);

      // load all model ids to generate
      List<Integer> modelIDs = loadModelIDs(conn);
      
      // keep track of the status
      FileWriter logger = logStatus ? new FileWriter("./Progress.txt") : null;
      long start1 = System.currentTimeMillis();   
      
      // generate test case for each model
      List<Integer> notGen     = new ArrayList<Integer>();
      List<Integer> fullGen    = new ArrayList<Integer>();
      List<Integer> partialGen = new ArrayList<Integer>();
      for (int i = fromModelID - 1, size = modelIDs.size(); i < toModelID - 1 && i < size; i++) {
        int modelID = modelIDs.get(i);
        
        // skip this model if it is in the filter list
        if (m_filterModelIDs.contains(modelID)) {
          System.out.println("Skip model with id: " + (i + 1));
          continue;
        }
        
        // load the model to generate
        Object[] model = loadModel(conn, modelID);
        if (model != null) {
          // log progress
          String progress = "Generating for modelID: " + modelID + "... (" + modelIDs.size() + ")";
          System.out.println(progress);
          if (logStatus) {
            logger.write(progress);
            logger.flush();
          }

          // start time
          long start2 = System.currentTimeMillis();
          String genStatus = genTestCase(modelID, model, fullGen, partialGen, notGen, maxTimeAllow, allowRelaxGen);
          
          // end time
          if (logStatus) {
            long end = System.currentTimeMillis();
            logger.write(". " + genStatus);
            logger.write(" Elapsed time: " + (end - start2) + "ms.");
            logger.write(" Global Status: " + fullGen.size() + " / " + partialGen.size() + " / " + notGen.size() + "\n");
            logger.flush();
          }
        }
        else {
          System.err.println("Cannot load model with id: " + modelID + ", skip!");
        }
      }
      System.out.println();
      
      System.out.println("Models fully generated (" + fullGen.size() + "): ");
      for (Integer modelID : fullGen) {
        System.out.println(modelID);
      }
      System.out.println();
      
      System.out.println("Models partially generated (" + partialGen.size() + "): ");
      for (Integer modelID : partialGen) {
        System.out.println(modelID);
      }
      System.out.println();
      
      System.out.println("Models not generated (" + notGen.size() + "): ");
      for (Integer modelID : notGen) {
        System.out.println(modelID);
      }
      System.out.println();

      // end time
      long end = System.currentTimeMillis();
      String time = "Total elapsed: " + (end - start1) + "ms";
      System.out.println(time);
      if (logStatus) {
        logger.write(time + "\n");
        logger.flush();
        logger.close();
      }
    } catch (Exception e) {
      e.printStackTrace();
    } finally {
      DbHelperSqlite.closeConnection(conn);
    }
  }
  
  /**
   * @param allowRelaxGen: use a simple callee when the precise callee cannot be generated
   */
  @SuppressWarnings("unchecked")
  private String genTestCase(int modelID, Object[] model, List<Integer> fullGen, 
      List<Integer> partialGen, List<Integer> notGen, long maxTimeAllow, boolean allowRelaxGen) {

    String genStatus = null;
    try {
      // get method
      CallStack cs = (CallStack) model[0];
      IR ir = Jar2IR.getIR(m_generator.getWalaAnalyzer(), cs.getCurMethodNameOrSign(), cs.getCurLineNo());
      
      // read and create requirement for each parameter
      Requirements requirements = Requirements.createRequirements((String) model[1], ir, m_generator.getWalaAnalyzer());
  
      // if calling a constructor, then v1 != null is not useful
      if (ir.getMethod().isInit()) {
        requirements.removeRequirement("v1");
      }
      
      // generate sequence for each instance
      VarNamePool varNamePool = new VarNamePool();
      GenerationResult genResult = invokeGenThread(requirements, maxTimeAllow, varNamePool);
      
      int fullGenSize = genResult.getSequenceCount();
      boolean fullyGen = fullGenSize == requirements.size() || 
                         (m_allowStaticNotSat && onlyStaticNotSat(requirements, genResult));
      
      // obtain generation status for each variable: 
      genStatus = "(Generated: ";
      for (String varName : genResult.getGenOrder()) {
        genStatus += varName + "|";
      }
      genStatus += ").";
      
      // if we allow relax generation, generate a simple callee
      if (allowRelaxGen && !ir.getMethod().isStatic() && !ir.getMethod().isInit() && genResult.getSequence("v1") == null) {
        System.out.println("Relax generation mode is on, a simple callee object will be generated.");
        
        // re-create reqsMap as the target instances could have been changed
        requirements = Requirements.createRequirements((String) model[1], ir, m_generator.getWalaAnalyzer());
        
        Sequence genCalleeSeq = generateSimpleCallee(requirements, ir, maxTimeAllow, varNamePool);
        if (genCalleeSeq != null) {
          genResult.addSequence("v1", genCalleeSeq);
        }
      }
      
      // save test case
      if (genResult.getSequenceCount() > 0) {
        
        // output to console
        System.out.println(fullGenSize + " / " + requirements.size() + " requirements have been generated!");
        
        for (String varName : genResult.getGenOrder()) {
          Sequence sequence = genResult.getSequence(varName);
          System.out.println(varName + ": ");
          System.out.println(sequence.toString());
          System.out.println("key variable: " + (sequence.getKeyVariable() == null ? "N/A" : 
                                                 sequence.getKeyVariable().getVarName()));
        }
        
        if (fullyGen) {
          fullGen.add(modelID);
        }
        else {
          partialGen.add(modelID);
        }
        
        // generate actual source code
        String sourceCode = genSourceCode(genResult, ir);
        sourceCode = renameVariables(sourceCode);
  
        // create inner extends classes when necessary
        Object[] genInnerResult = genInnerClasses(genResult, ir);
        String innerClasses = (String) genInnerResult[0];
        Hashtable<IClass, HashSet<IR>> extendedClasses = (Hashtable<IClass, HashSet<IR>>) genInnerResult[1];
        
        // find default method invocation
        String pkgName = findDefaultInvocation(extendedClasses);
        if (pkgName.length() == 0) {
          pkgName = findDefaultAssignment(genResult);
        }
        
        // write to file
        m_junitFileWriter.writeTestCase(sourceCode, innerClasses, pkgName, modelID, fullyGen);
      }
      else {
        notGen.add(modelID);
        System.err.println("Failed to generate sequence for model with id: " + modelID);
      }
    } catch (Exception e) {
      notGen.add(modelID);
      e.printStackTrace();
    }
    
    return genStatus;
  }
  
  @SuppressWarnings("deprecation")
  private GenerationResult invokeGenThread(Requirements requirements, long maxTimeAllow, 
      VarNamePool varNamePool) throws InterruptedException {
    
    // generate sequence for each instance
    GenerationThread genThread = new GenerationThread();
    genThread.setRequirementsToGen(requirements, m_generator, varNamePool);
    genThread.start();

    // timeout
    long startGen = System.currentTimeMillis();
    while (genThread.isAlive() && (System.currentTimeMillis() - startGen) < maxTimeAllow) {
      Thread.sleep(25);
    }
    // stop long run methods
    boolean timeout = genThread.isAlive();
    if (timeout) {
      System.err.println("Sequence generation timeout! Tiggering stop flag...");
      genThread.setStopFlag();
      
      long setStopTime = System.currentTimeMillis();
      while (genThread.isAlive() && (System.currentTimeMillis() - setStopTime) < 5000) {
        Thread.sleep(25); // wait for stop flag to take effect
      }

      if (genThread.isAlive()) {
        System.err.println("Stop flag is not working, terminating generation thread...");
        genThread.stop();
        Thread.sleep(1000);
        System.err.println("Generation thread terminated!");
      }
      else {
        System.err.println("Generation thread stopped gracefully!");
      }
    }
    
    return genThread.getLastGenResult();
  }
  
  private Sequence generateSimpleCallee(Requirements origRequirements, IR ir, 
      long maxTimeAllow, VarNamePool origVarNamePool) throws InterruptedException {
    
    Sequence sequence = null;
    
    Condition notNullCond = null;
    Requirement origReq = origRequirements.getRequirement("v1");
    for (Condition reqCond : origReq.getConditions()) {
      if (reqCond.getOnlyBinaryTerm() != null && 
          reqCond.getOnlyBinaryTerm().toString().equals("v9999 != null")) {
        notNullCond = reqCond;
        break;
      }
    }
    
    if (notNullCond != null) {
      Requirement simpleCalleeReq = new Requirement("v1");
      simpleCalleeReq.addCondition(notNullCond);
      boolean useInnerClass = !ir.getMethod().isStatic() && !ir.getMethod().isPublic();
      simpleCalleeReq.setTargetInstance(notNullCond.getOnlyBinaryTerm().getInstance1(), useInnerClass);
      Requirements requirements = new Requirements();
      requirements.addRequirement("v1", simpleCalleeReq);
      
      GenerationResult genResult = invokeGenThread(requirements, maxTimeAllow, origVarNamePool);
      sequence = genResult.getSequence("v1");
    }
    
    return sequence;
  }
  
  private boolean onlyStaticNotSat(Requirements requirements, GenerationResult genResult) {
    boolean onlyStaticNotSat = true;
    
    Enumeration<String> keys = requirements.keys();
    while (keys.hasMoreElements() && onlyStaticNotSat) {
      String key = (String) keys.nextElement();
      Sequence seq = genResult.getSequence(key);
      if (seq == null && !key.startsWith("L")) {
        onlyStaticNotSat = false;
      }
    }
    return onlyStaticNotSat;
  }
  
  private List<Integer> loadModelIDs(Connection conn) throws Exception {
    List<Integer> modelIDs = new ArrayList<Integer>();
    
    String sqlText = "Select id From " + m_tableName;
    ResultSet rs = DbHelperSqlite.executeQuery(conn, sqlText);
    while (rs.next()) {
      modelIDs.add(rs.getInt(1));
    }
    rs.close();
    
    return modelIDs;
  }
  
  private Object[] loadModel(Connection conn, int modelID) throws Exception {
    Object[] model = null;
    
    String sqlText = "Select CallStack, ModelString From " + m_tableName + " Where id = " + modelID;
    ResultSet rs = DbHelperSqlite.executeQuery(conn, sqlText);
    if (rs.next()) {
      model = new Object[] {CallStack.fromString(rs.getString(1)), rs.getString(2)};
    }
    rs.close();
    
    return model;
  }
  
  private String genSourceCode(GenerationResult genResult, IR ir) {
    StringBuilder sourceCode = new StringBuilder();
    
    // append sources for creating parameters
    for (String varName : genResult.getGenOrder()) {
      Sequence seq = genResult.getSequence(varName);
      if (seq != null) {
        sourceCode.append(seq.toString());
      }
    }
    
    // append method invocation
    IMethod method = ir.getMethod();
    if (method.isInit()) {
      sourceCode.append("    new ").append(Utils.getClassTypeJavaStr(method.getDeclaringClass().getName().toString()));
    }
    else {
      String caller = null;
      if (method.isStatic()) {
        caller = Utils.getClassTypeJavaStr(method.getDeclaringClass().getName().toString());
      }
      else {
        Sequence seq = genResult.getSequence("v1");
        if (seq != null) {
          caller = seq.getKeyVariable().getVarName();
        }
        else {
          String varType = ir.getParameterType(0).getName().toString();
          caller = "// " + Utils.getTypeRandomValue(varType.equals("J") ? "I" : varType); // avoid null dereference
        }
      }
      sourceCode.append("    ").append(caller).append(".").append(method.getName().toString());
    }
    
    // append the parameters of invocation
    sourceCode.append("(");
    for (int i = method.isStatic() ? 0 : 1, size = ir.getNumberOfParameters(); i < size; i++) {
      String paramName   = "v" + (i + 1);
      String paramType = ir.getParameterType(i).getName().toString();

      // the corresponding real variable name
      Sequence seq = genResult.getSequence(paramName);
      String realParamName = null;
      if (seq != null) {
        realParamName = seq.getKeyVariable().getVarName();
      }
      else {
        realParamName = Utils.getTypeRandomValue(paramType.equals("J") ? "I" : paramType);
        realParamName = paramType.equals("C") ? "'" + realParamName + "'" : realParamName;
      }
      
      // append the parameters
      if (Utils.isPrimitiveType(paramType)) {
        paramType = Utils.getClassTypeJavaStr(paramType);
        sourceCode.append("(").append(paramType).append(") ");
      }
      else {
        Class<?> cls = Utils.findClass(paramType);
        if (cls != null && Modifier.isPublic(cls.getModifiers())) {
          paramType = Utils.getClassTypeJavaStr(paramType);
          sourceCode.append("(").append(paramType).append(") ");
        }
      }
      sourceCode.append(realParamName);
      if (i != size - 1) {
        sourceCode.append(", ");
      }
    }
    sourceCode.append(");\n");
    
    return sourceCode.toString();
  }

  private static final Pattern s_patternVarDef    = Pattern.compile(" (v[\\d]+) = ");
  private static final Pattern s_patternVarDefUse = Pattern.compile("\\W(v[\\d]+)\\D");
  private String renameVariables(String sourceCode) {
    StringBuilder newSourceCode = new StringBuilder();
    
    // find all variable defines
    Hashtable<String, String> varNameMap = new Hashtable<String, String>();
    Matcher matcher = s_patternVarDef.matcher(sourceCode);
    while (matcher.find()) {
      String varName = matcher.group(1);
      if (!varNameMap.containsKey(varName)) {
        varNameMap.put(varName, "v" + (varNameMap.size() + 1));
      }
    }
    
    // replace all variable appearances
    int currentPos = 0;
    matcher = s_patternVarDefUse.matcher(sourceCode);
    for(int lastEnd = -1; matcher.find(); currentPos = lastEnd) {
      String varName = matcher.group(1);
      lastEnd = matcher.end(1);
      
      newSourceCode.append(sourceCode.subSequence(currentPos, lastEnd - varName.length()));
      String newVarName = varNameMap.get(varName);
      newSourceCode.append((newVarName != null) ? newVarName : varName);
    }
    newSourceCode.append(sourceCode.subSequence(currentPos, sourceCode.length()));
    
    return newSourceCode.toString();
  }
  
  private Object[] genInnerClasses(GenerationResult genResult, IR ir) {
    StringBuilder innerClassCode = new StringBuilder();
    
    // create inner extends classes when necessary
    Hashtable<IClass, HashSet<IR>> nonPublicMap = new Hashtable<IClass, HashSet<IR>>();
    
    // collect all non-public invocations
    for (String varName : genResult.getGenOrder()) {
      Sequence seq = genResult.getSequence(varName);
      if (seq != null) {
        for (Statement statement : seq.getStatements()) {
          if (statement instanceof InvocationStatement) {
            InvocationStatement invokeStmt = (InvocationStatement) statement;
            
            IR invokeTarget = invokeStmt.getMethod();
            if (invokeTarget != null) {
              IClass declClass    = invokeTarget.getMethod().getDeclaringClass();
              Class<?> declClass2 = Utils.findClass(declClass.getName().toString());
              
              // 1) invoking a non-public method, 2) the declClass is non-public 3) init() an abstract class
              if (!invokeTarget.getMethod().isPublic() || ((!Modifier.isPublic(declClass2.getModifiers()) || 
                   Modifier.isAbstract(declClass2.getModifiers())) && invokeTarget.getMethod().isInit())) {
                
                IClass toExtend    = declClass;
                Class<?> toExtend2 = declClass2;
                
                Variable callee = statement.getVariables().get(0);
                IClass calleeClass = WalaUtils.getClass(m_generator.getWalaAnalyzer(), callee.getClassName());
                if (calleeClass != null && !declClass.equals(calleeClass) && 
                    !Modifier.isFinal(calleeClass.getModifiers()) ) {
                  
                  // extend the sub-class one
                  Class<?> calleeClass2 = Utils.findClass(calleeClass.getName().toString());
                  if (calleeClass2 != null && Utils.isSubClass(declClass2, calleeClass2)) {
                    toExtend  = calleeClass;
                    toExtend2 = calleeClass2;
                  }
                }
                
                // check one more time as toExtend may have been changed
                if (!invokeTarget.getMethod().isPublic() || ((!Modifier.isPublic(toExtend2.getModifiers()) || 
                     Modifier.isAbstract(toExtend2.getModifiers())) && invokeTarget.getMethod().isInit())) {
                  HashSet<IR> methods = nonPublicMap.get(toExtend);
                  if (methods == null) {
                    methods = new HashSet<IR>();
                    nonPublicMap.put(toExtend, methods);
                  }
                  
                  if (!invokeTarget.getMethod().isPublic()) {
                    methods.add(invokeTarget);
                  }
                }
              }
            }

            // also check about return type
            Variable assignTo = invokeStmt.getAssignTo();
            if (assignTo != null && assignTo.getClassName() != null) {
              // visibleName could be default, so we still need to add
              String visibleName = Statement.visibleClassName(assignTo.getClassName());
              addNonPublicClass(visibleName, nonPublicMap);
            }
          }
          else {
            AssignmentStatement assignStmt = (AssignmentStatement) statement;
            if (assignStmt.getOrigAssignToType() != null) {
              String assignToType = assignStmt.getOrigAssignToType();
              assignToType = assignToType.startsWith("[") ? assignToType.substring(1) : assignToType;
              addNonPublicClass(assignToType, nonPublicMap);
            }
          }
        }
      }
    }
    if (!ir.getMethod().isPublic()) {
      IClass declClass    = ir.getMethod().getDeclaringClass();
      Class<?> declClass2 = Utils.findClass(declClass.getName().toString());

      IClass toExtend    = declClass;
      Class<?> toExtend2 = declClass2;
      
      if (!ir.getMethod().isStatic() && genResult.getSequence("v1") != null) {
        Variable callee = genResult.getSequence("v1").getKeyVariable();
        IClass calleeClass = WalaUtils.getClass(m_generator.getWalaAnalyzer(), callee.getClassName());
        if (calleeClass != null && !declClass.equals(calleeClass) && !Modifier.isFinal(calleeClass.getModifiers())) {
          // extend the sub-class one
          Class<?> calleeClass2 = Utils.findClass(calleeClass.getName().toString());
          if (calleeClass2 != null && Utils.isSubClass(declClass2, calleeClass2)) {
            toExtend  = calleeClass;
            toExtend2 = calleeClass2;
          }
        }
      }
      
      // check one more time as toExtend may have been changed
      if (!ir.getMethod().isPublic() || ((!Modifier.isPublic(toExtend2.getModifiers()) || 
          Modifier.isAbstract(toExtend2.getModifiers())) && ir.getMethod().isInit())) {
        HashSet<IR> methods = nonPublicMap.get(toExtend);
        if (methods == null) {
          methods = new HashSet<IR>();
          nonPublicMap.put(toExtend, methods);
        }
        if (!ir.getMethod().isPublic()) {
          methods.add(ir);
        }
      }
    }
    
    // find class enclosing relationships
    int oldSize = -1;
    List<IClass[]> enclosings = null;
    while (oldSize != nonPublicMap.size()) {
      oldSize = nonPublicMap.size();
      enclosings = new ArrayList<IClass[]>();
      
      // check each class
      Enumeration<IClass> keys = nonPublicMap.keys();
      while (keys.hasMoreElements()) {
        IClass key = (IClass) keys.nextElement();
        int index = key.getName().toString().lastIndexOf('$');
        if (index >= 0) {
          String upperClassName = key.getName().toString().substring(0, index);
          IClass upperClass = WalaUtils.getClass(m_generator.getWalaAnalyzer(), upperClassName);
          if (upperClass != null) {
            if (!nonPublicMap.containsKey(upperClass)) {
              nonPublicMap.put(upperClass, new HashSet<IR>());
            }
            enclosings.add(new IClass[] {upperClass, key});
          }
        }
      }
    }

    // generate extends codes for classes whose protected methods will be called
    Hashtable<IClass, String> extendsCodeMap = new Hashtable<IClass, String>();
    Enumeration<IClass> keys = nonPublicMap.keys();
    while (keys.hasMoreElements()) {
      IClass key    = (IClass) keys.nextElement();
      Class<?> key2 = Utils.findClass(key.getName().toString());
      HashSet<IR> nonPublicMethods = nonPublicMap.get(key);
      
      // only extend protected methods
      HashSet<IR> protectedMethods = new HashSet<IR>();
      for (IR nonPublicMethod : nonPublicMethods) {
        if (nonPublicMethod.getMethod().isProtected()) {
          protectedMethods.add(nonPublicMethod);
        }
      }

      if (protectedMethods.size() > 0 || 
          (Modifier.isPublic(key2.getModifiers()) || Modifier.isProtected(key2.getModifiers()))) {
        String genCode = ExtendClassUtils.extendClass(m_generator.getWalaAnalyzer(), key, protectedMethods);
        extendsCodeMap.put(key, genCode);
      }
    }
    
    // merge according to enclosing relationships, simple but is enough in reality
    HashSet<IClass> appended = new HashSet<IClass>();
    for (IClass[] enclosing : enclosings) {
      String outerCode = extendsCodeMap.get(enclosing[0]);
      String innerCode = extendsCodeMap.get(enclosing[1]);
      
      if (outerCode != null && innerCode != null) {
        String enclosedOuterCode = ExtendClassUtils.encloseClass(outerCode, innerCode);
        extendsCodeMap.put(enclosing[0], enclosedOuterCode);
        
        int index = innerClassCode.indexOf(outerCode);
        if (index >= 0) {
          // the outer class has already been written, replace it
          innerClassCode.replace(index, index + outerCode.length(), enclosedOuterCode);
        }
        else {
          innerClassCode.append(enclosedOuterCode).append("\n");
        }
        appended.add(enclosing[0]);
        appended.add(enclosing[1]);  
      }
    }
    
    // append the rest
    keys = nonPublicMap.keys();
    while (keys.hasMoreElements()) {
      IClass key = keys.nextElement();
      String extendCode = extendsCodeMap.get(key);
      if (!appended.contains(key) && extendCode != null) {
        // not all classes need to be extended, only the ones 
        // containing called protected methods are necessary
        for (IR nonPublic : nonPublicMap.get(key)) {
          if (nonPublic.getMethod().isProtected()) {
            innerClassCode.append(extendCode);
            break;
          }
        }
      }
    }
    
    return new Object[] {innerClassCode.toString(), nonPublicMap};
  }
  
  private void addNonPublicClass(String className, Hashtable<IClass, HashSet<IR>> nonPublicMap) {
    IClass clazz = WalaUtils.getClass(m_generator.getWalaAnalyzer(), className);
    if (clazz != null) {
      Class<?> clazz2 = Utils.findClass(clazz.getName().toString());
      if (clazz2 != null && !Modifier.isPublic(clazz2.getModifiers())) {
        HashSet<IR> methods = nonPublicMap.get(clazz2);
        if (methods == null) {
          methods = new HashSet<IR>();
          nonPublicMap.put(clazz, methods);
        }
      }
    }
  }
  
  private String findDefaultInvocation(Hashtable<IClass, HashSet<IR>> extendedClasses) {
    String pkgName = "";
    
    Enumeration<IClass> keys = extendedClasses.keys();
    while (keys.hasMoreElements() && pkgName.length() == 0) {
      IClass key = (IClass) keys.nextElement();
      String declClassName = key.getName().toString();
      
      HashSet<IR> methods = extendedClasses.get(key);
      for (IR ir : methods) {
        if (!ir.getMethod().isPublic() && !ir.getMethod().isPrivate() && !ir.getMethod().isProtected()) {
          int index = declClassName.lastIndexOf('/');
          if (index >= 0) {
            pkgName = Utils.getClassTypeJavaStr(declClassName.substring(0, index));
          }
        }
        if (pkgName.length() != 0) {
          break;
        }
      }
      
      // if the class itself is default, also generate package name
      if (pkgName.length() == 0) {
        Class<?> declClass = Utils.findClass(key.getName().toString());
        if (!Modifier.isPublic(declClass.getModifiers()) && 
            !Modifier.isPrivate(declClass.getModifiers()) && !Modifier.isProtected(declClass.getModifiers())) {
          int index = declClassName.lastIndexOf('/');
          if (index >= 0) {
            pkgName = Utils.getClassTypeJavaStr(declClassName.substring(0, index));
          }
        }
      }
    }
    
    return pkgName;
  }
  
  private String findDefaultAssignment(GenerationResult genResult) {
    String pkgName = "";
    
    List<String> genOrder = genResult.getGenOrder();
    for (int i = 0, size = genOrder.size(); i < size && pkgName.length() == 0; i++) {
      String varName = genOrder.get(i);
      Sequence seq = genResult.getSequence(varName);
      if (seq != null) {
        for (int j = 0, size2 = seq.getStatements().size(); j < size2 && pkgName.length() == 0; j++) {
          if (seq.getStatements().get(j) instanceof AssignmentStatement) {
            AssignmentStatement assignStatement = (AssignmentStatement) seq.getStatements().get(j);
            String declClassType = assignStatement.getFieldDeclClassType();
            
            // found a direct assignment to field
            if (declClassType != null) {
              String assignToName = assignStatement.getAssignTo().getVarName();
              String fieldName = assignToName.substring(assignToName.lastIndexOf('.') + 1);
              Class<?> declClass = Utils.findClass(declClassType);
              Field field = Utils.findClassField(declClass, fieldName);
              
              if (field != null && !Modifier.isPublic(field.getModifiers()) && 
                                   !Modifier.isPrivate(field.getModifiers()) && 
                                   !Modifier.isProtected(field.getModifiers())) {
                pkgName = declClass.getPackage().getName();
              }
            }
          }
        }
      }
    }
    
    return pkgName;
  }

  private HashSet<Integer> readFilterModelIDs(String filterModelIDsFile) {
    HashSet<Integer> filterList = new HashSet<Integer>();
    
    if (filterModelIDsFile != null) {
      try {
        BufferedReader reader = new BufferedReader(new FileReader(filterModelIDsFile));
        
        String line;
        while ((line = reader.readLine()) != null) {
          try {
            filterList.add(Integer.parseInt(line));
          } catch (NumberFormatException e) {
            continue;
          }
        }
        reader.close();
      } catch (IOException e) {}
    }
    return filterList;
  }

  private HashSet<String> readFilterMethods(String filterMethodsFile) {
    HashSet<String> filterList = new HashSet<String>();
    
    if (filterMethodsFile != null) {
      try {
        BufferedReader reader = new BufferedReader(new FileReader(filterMethodsFile));
        
        String line;
        while ((line = reader.readLine()) != null) {
          try {
            filterList.add(line);
          } catch (NumberFormatException e) {
            continue;
          }
        }
        reader.close();
      } catch (IOException e) {}
    }
    return filterList;
  }
  
  @SuppressWarnings("unused")
  private void analysis(String progressFile, boolean oneEachBranchFirstline, boolean removePrimitives) {
    Connection conn = null;
    try {
      conn = DbHelperSqlite.openConnection(m_dbName);

      // load all model ids to generate
      List<Integer> modelIDs = loadModelIDs(conn);
      
      HashSet<Integer> modelIDsToAnalyze = new HashSet<Integer>();
      // retain only one model for each branchfirstline
      if (oneEachBranchFirstline) {
        HashSet<Integer> branchFirstLines = new HashSet<Integer>();
        for (int i = 0, size = modelIDs.size(); i < size; i++) {
          int modelID = modelIDs.get(i);

          Object[] model = loadModel(conn, modelID);
          if (model != null) {
            int branchFirstLineID = (Integer) model[0];
            if (!branchFirstLines.contains(branchFirstLineID)) {
              modelIDsToAnalyze.add(modelID);
              branchFirstLines.add(branchFirstLineID);
            }
          }
        }
      }
      else {
        modelIDsToAnalyze.addAll(modelIDs);
      }
      
      // load all requirements
      Hashtable<Requirement, Integer> allRequirements = new Hashtable<Requirement, Integer>();
      Hashtable<String, Integer> reqIndexMap = new Hashtable<String, Integer>();
      for (int i = 0, size = modelIDs.size(); i < size; i++) {
        int modelID = modelIDs.get(i);

        if (!modelIDsToAnalyze.contains(modelID)) {
          continue;
        }
        
        Object[] model = loadModel(conn, modelID);
        if (model != null) {
          // get method
          CallStack cs = (CallStack) model[1];
          String methodName = cs.getCurMethodNameOrSign();
          int lineNo = cs.getCurLineNo();
          IR ir = Jar2IR.getIR(m_generator.getWalaAnalyzer(), methodName, lineNo);
          
          // read and create requirements
          Requirements requirements = Requirements.createRequirements((String) model[2], ir, m_generator.getWalaAnalyzer());

          // assign index to each requirement
          Enumeration<String> keys = requirements.keys();
          while (keys.hasMoreElements()) {
            String key = (String) keys.nextElement();
            Requirement req = requirements.getRequirement(key);
            if (req != null) {
              // skip primitives
              if (removePrimitives && req.getConditions().size() == 1 && 
                  req.getConditions().get(0).getOnlyBinaryTerm() != null && 
                  req.getConditions().get(0).getOnlyBinaryTerm().getInstance2().getValue().startsWith("#!")) {
                continue;
              }
              
              // the requirement may exist already
              Integer index = allRequirements.get(req);
              if (index == null) {
                index = allRequirements.size();
                allRequirements.put(req, index);
              }
              reqIndexMap.put(String.valueOf(modelID) + "_" + key, index);
            }
          }
        }
        else {
          System.err.println("Cannot load model with id: " + modelID + ", skip!");
        }
      }
      
      // read progress file
      HashSet<Integer> generatedReqs = new HashSet<Integer>();
      try {
        BufferedReader reader = new BufferedReader(new FileReader(progressFile));
        
        String line = null;
        while ((line = reader.readLine()) != null) {
          int index1 = line.indexOf("Generating for modelID: ");
          int index2 = line.indexOf(".");
          if (index1 >= 0 && index2 >= 0) {
            int modelID = Integer.parseInt(line.substring(index1 + 24, index2));
            
            if (!modelIDsToAnalyze.contains(modelID)) {
              continue;
            }
            
            index1 = line.indexOf("(Generated: ");
            if (index1 >= 0) {
              index2 = line.indexOf(')', index1 + 12);
              if (index2 >= 0) {
                String genParams = line.substring(index1 + 12, index2);
                if (genParams.length() > 0) {
                  String[] paramNames = genParams.split("\\|");
                  for (String paramName : paramNames) {
                    String key = String.valueOf(modelID) + "_" + paramName;
                    Integer reqIndex = reqIndexMap.get(key);
                    if (reqIndex != null) {
                      generatedReqs.add(reqIndex);
                    }
                  }
                }
              }
            }
          }
        }
        
        reader.close();
      } catch (Exception e) {e.printStackTrace();}
      
      // show statistic
      int totalReq = 0;
      int totalReqComplex = 0;
      int totalGen = 0;
      int totalGenComplex = 0;
      int[] reqDistribution    = new int[10];
      int[] reqGenDistribution = new int[10];
      Enumeration<Requirement> keys = allRequirements.keys();
      while (keys.hasMoreElements()) {
        Requirement key = (Requirement) keys.nextElement();
        Integer reqIndex = allRequirements.get(key);
        
        int putTo = -1;
        int reqSize = key.getCompareStrings().size();
        if (reqSize > 0 && reqSize < 10) {
          putTo = reqSize - 1;
        }
        else if (reqSize >= 10) {
          putTo = 9;
        }
        
        if (putTo >= 0) {
          reqDistribution[putTo] += 1;
          totalReq++;
          totalReqComplex += (putTo > 0) ? 1 : 0;
          
          if (generatedReqs.contains(reqIndex)) {
            reqGenDistribution[putTo] += 1;
            totalGen++;
            totalGenComplex += (putTo > 0) ? 1 : 0;
          }
        }
      }
      
      for (int i = 0; i < 10; i++) {
        System.out.println("Requirement size " + (i + 1) + ": " + reqGenDistribution[i] + " / " + reqDistribution[i]);
      }
      System.out.println("Total: " + totalGen + " / " + totalReq);
      System.out.println("Complex: " + totalGenComplex + " / " + totalReqComplex);
      
    } catch (Exception e) {
      e.printStackTrace();
    } finally {
      DbHelperSqlite.closeConnection(conn);
    }
  }
  
  public static void main(String[] args) throws Exception {
    ModelTestGeneration generation = new ModelTestGeneration(
        args[0],                   /* jar file */
        args[1],                   /* pseudo implementation jar */
        args[2],                   /* java summary dir */
        args[3],                   /* other summary dir */
        args[4],                   /* model database name */
        args[5],                   /* target test case dir */
        args[6],                   /* filter model list file */
        args[7],                   /* filter method list file */
        Integer.parseInt(args[8]), /* max step */
        5,                         /* max sub-classes */
        Integer.parseInt(args[9]), /* accessibility */
        true);                     /* relax generation */
    
    int startModelID = Integer.parseInt(args[10]);
    if (args.length < 13) {
      generation.genTestCase(startModelID, Integer.parseInt(args[11]) /* max generation time */, true);
    }
    else {
      int endModelID = Integer.parseInt(args[11]);
      endModelID = endModelID < 0 ? Integer.MAX_VALUE : endModelID;
      generation.genTestCases(startModelID, endModelID, Integer.parseInt(args[12]) /* max generation time */, true, true);
    }
    //generation.analysis("./progress.txt", true, true);
  }
  
  private final String           m_dbName;
  private final String           m_tableName;
  private final Generator        m_generator;
  private final JunitFileWriter  m_junitFileWriter;
  private final HashSet<Integer> m_filterModelIDs;
  private final boolean          m_allowStaticNotSat;
}
