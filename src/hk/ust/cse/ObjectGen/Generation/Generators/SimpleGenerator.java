package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.TestCase.AssignmentStatement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class SimpleGenerator extends AbstractGenerator {
  
  public SimpleGenerator(Generator allTypeGenerator, int accessibility) {
    super(allTypeGenerator, accessibility);
  }

  @Override
  public Sequence generate(Requirement req, List<Requirement> ancestorReqs) {
    Sequence seq = null;
    
    if (req.containsCondition("v9999 != null")) {
      if (req.getTargetType() == java.net.URL.class) {
        seq = createURL();
      }
      else if (req.getTargetType() == java.math.BigDecimal.class) {
        seq = createBigDecimal();
      }
      else if (req.getTargetType() == java.math.BigInteger.class) {
        seq = createBigInteger();
      }
      else if (req.getTargetType() == java.io.File.class && !req.containsString("__prop__") && 
                                                            !req.containsString("__state__")) {
        seq = createFile();
      }
      else if (req.getTargetType() == java.lang.Package.class) {
        seq = createPackage();
      }
      else if (req.getTargetType() == java.net.InetAddress.class) {
        seq = createInetAddress();
      }
      else if (req.getTargetType() == java.lang.String.class && req.containsCondition("v9999 == ##%existing_file%")) {
        seq = createExistingFilePath();
      }
      else if (req.getConditions().size() == 1) {
        seq = tryUseStaticField(req.getTargetInstance().getLastRefType());
      }
    }
    return seq;
  }
  
  private Sequence createURL() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("\"http://localhost\"", "Ljava/lang/String");
    parameters.put("v2", param1);
    return createObject("Ljava/net/URL", "java.net.URL.<init>(Ljava/lang/String;)V", parameters);
  }
  
  private Sequence createBigDecimal() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("0", "I");
    parameters.put("v2", param1);
    return createObject("Ljava/math/BigDecimal", "java.math.BigDecimal.<init>(I)V", parameters);
  }
  
  private Sequence createBigInteger() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("\"0\"", "Ljava/lang/String");
    parameters.put("v2", param1);
    return createObject("Ljava/math/BigInteger", "java.math.BigInteger.<init>(Ljava/lang/String;)V", parameters);
  }
  
  private Sequence createFile() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("\"./\"", "Ljava/lang/String");
    parameters.put("v2", param1);
    return createObject("Ljava/io/File", "java.io.File.<init>(Ljava/lang/String;)V", parameters);
  }
  
  private Sequence createExistingFilePath() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("java.io.File.createTempFile(\"star-\", \".tmp\", new java.io.File(\"./\"))", "Ljava/io/File");
    parameters.put("v1", param1);
    return createObject("Ljava/lang/String", "java.io.File.getPath()Ljava/lang/String;", parameters);
  }
  
  private Sequence createPackage() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("\"java.lang\"", "Ljava/lang/String");
    parameters.put("v1", param1);
    return createObject("Ljava/lang/Package", "java.lang.Package.getPackage(Ljava/lang/String;)Ljava/lang/Package;", parameters);
  }
  
  private Sequence createInetAddress() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    return createObject("Ljava/net/InetAddress", "java.net.InetAddress.getLocalHost()Ljava/net/InetAddress;", parameters);
  }
  
  private Sequence createObject(String className, String ctorSig, Hashtable<String, Variable> parameters) {
    Sequence seq = null;

    IR ir = Jar2IR.getIR(m_allTypeGenerator.getWalaAnalyzer(), ctorSig);
    if (ir != null) {
      Variable keyVariable = new Variable(nextVariableName(), className);
      seq = new Sequence(keyVariable);
      Hashtable<String, Variable> allParams = new Hashtable<String, Variable>();
      allParams.put("v1", keyVariable);
      allParams.putAll(parameters);
      seq.addMethod(ir, allParams, false);
    }
    return seq;
  }

  private Sequence tryUseStaticField(String className) {
    Sequence seq = null;
    
    Class<?> targetClass = className != null ? Utils.findClass(className) : null;
    if (targetClass != null) {
      for (Field field : Utils.getInheritedFields(targetClass)) {
        int mod = field.getModifiers();
        if (Modifier.isPublic(mod) && Modifier.isStatic(mod) && Modifier.isFinal(mod)) {
          try {
            Object fieldObj = field.get(null);
            if (fieldObj != null && Utils.isSubClass(targetClass, fieldObj.getClass())) {
              String pubClassName = Utils.getClosestPublicSuperClass(targetClass).getName();
              Variable assignTo   = new Variable(nextVariableName(), pubClassName);
              Variable assignFrom = new Variable(Utils.getClassTypeJavaStr(
                  field.getDeclaringClass().getName()) + "." + field.getName(), pubClassName);
              seq = new Sequence(assignTo);
              seq.addStatement(new AssignmentStatement(assignTo, assignFrom));
            }
          } catch (Exception e) {}
        }
      }
    }
    
    return seq;
  }
}
