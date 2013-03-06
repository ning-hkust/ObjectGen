package hk.ust.cse.ObjectGen.Generation.Generators;

import hk.ust.cse.ObjectGen.Generation.Generator;
import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Generation.TestCase.Variable;
import hk.ust.cse.Wala.Jar2IR;

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
    if (onlyVarNotNullReq(req)) {
      String typeName = req.getRequirementTerm(0).getInstance1().getLastRefType();
      if (typeName.equals("Ljava/net/URL")) {
        seq = createURL();
      }
      else if (typeName.equals("Ljava/math/BigDecimal")) {
        seq = createBigDecimal();
      }
      else if (typeName.equals("Ljava/math/BigInteger")) {
        seq = createBigInteger();
      }
      else if (typeName.equals("Ljava/io/File")) {
        seq = createFile();
      }
      else if (typeName.equals("Ljava/lang/Package")) {
        seq = createPackage();
      }
      else if (typeName.equals("Ljava/net/InetAddress")) {
        seq = createInetAddress();
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
  
  private Sequence createPackage() {
    Hashtable<String, Variable> parameters = new Hashtable<String, Variable>();
    Variable param1 = new Variable("\"java.lang\"", "Ljava/lang/String");
    parameters.put("v1", param1);
    return createObject("Ljava/lang/Package", "java.lang.Package.getPackage(Ljava/lang/String;)Ljava/lang/Package", parameters);
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
}
