package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Instance.INSTANCE_OP;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision.VirtualMachine.Relation;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.Wala.WalaUtils;
import hk.ust.cse.util.Utils;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.ibm.wala.ssa.IR;

public class Requirements {

  public Requirements() {
    m_reqsMap = new Hashtable<String, Requirement>();
  }
  
  public void addRequirement(String topVarName, Requirement req) {
    m_reqsMap.put(topVarName, req);
  }
  
  public Requirement getRequirement(String topVarName) {
    return m_reqsMap.get(topVarName);
  }
  
  public void removeRequirement(String topVarName) {
    m_reqsMap.remove(topVarName);
  }

  public int size() {
    return m_reqsMap.size();
  }
  
  public Enumeration<String> keys() {
    return m_reqsMap.keys();
  }

  public void setEnsureGenOrder(List<String> genOrder) {
    m_ensureGenOrder = genOrder;
  }
  
  public List<String> getEnsureGenOrder() {
    return m_ensureGenOrder;
  }
  
  public String toString() {
    StringBuilder str = new StringBuilder();
    
    Enumeration<String> keys = m_reqsMap.keys();
    while (keys.hasMoreElements()) {
      String varName = (String) keys.nextElement();
      Requirement childReq = m_reqsMap.get(varName);
      str.append(varName + ": " + childReq.getConditions()).append("\n");
    }
    return str.toString();
  }
  
  public static Requirements createRequirements(String modelStr, IR ir, WalaAnalyzer walaAnalyzer) {
    Requirements requirements = new Requirements();
    
    String[] modelLines = modelStr.split("\n");
    
    // retrieve explicit type information first
    Hashtable<String, String> nameTypeMap = new Hashtable<String, String>();
    for (int i = 1; i < modelLines.length; i++) {
      if (modelLines[i].contains(" instanceOf(")) { // instancecOf statement, this is the deprecated format
        handleInstanceOf(modelLines[i], nameTypeMap);
      }
      else if (modelLines[i].contains(" instanceof ")) { // instancecof statement, this is the new format
        handleInstanceof(modelLines[i], nameTypeMap);
      }
    }
    
    // create requirement terms
    Hashtable<String, Instance> nameInstanceMap    = new Hashtable<String, Instance>();
    Hashtable<String, Instance> topNameInstanceMap = new Hashtable<String, Instance>();
    Hashtable<Instance, String> instanceNameMap    = new Hashtable<Instance, String>();
    Hashtable<Instance, String> instanceModelMap   = new Hashtable<Instance, String>();
    Hashtable<String, List<Instance>> modelInstanceMap = new Hashtable<String, List<Instance>>();
    for (int i = 1; i < modelLines.length; i++) {
      if (!modelLines[i].startsWith("(") && !modelLines[i].contains(" instanceOf(")) { // non-array model term
        parseFieldAccess(modelLines[i], ir, 
            modelInstanceMap, nameInstanceMap, instanceNameMap, instanceModelMap, topNameInstanceMap);
      }
    }
    for (int i = 1; i < modelLines.length; i++) {
      if (!modelLines[i].startsWith("(") && !modelLines[i].contains(" instanceOf(")) { // non-array model term
        BinaryConditionTerm term = parseFieldModelTerm(walaAnalyzer, modelLines[i], ir, 
            nameTypeMap, modelInstanceMap, nameInstanceMap, instanceModelMap);
        if (term != null) {
          addToRequirements(requirements, new Condition(term), topNameInstanceMap);
        }
      }
    }
    for (int i = 1; i < modelLines.length; i++) {
      if (modelLines[i].startsWith("(") && !modelLines[i].contains(" instanceOf(")) { // array model term
        List<BinaryConditionTerm> terms = parseArrayModelTerm(modelLines[i], nameTypeMap, 
            nameInstanceMap, instanceNameMap, modelInstanceMap, instanceModelMap);
        if (terms != null && terms.size() > 0) {
          for (BinaryConditionTerm term : terms) {
            addToRequirements(requirements, new Condition(term), topNameInstanceMap);
          }
        }
      }
    }
    
    // set target instance for each requirement
    Enumeration<String> keys = requirements.keys();
    while (keys.hasMoreElements()) {
      String key = (String) keys.nextElement();
      Requirement req = requirements.getRequirement(key);
      
      boolean useInnerClass = !ir.getMethod().isStatic() && key.equals("v1") && !ir.getMethod().isPublic();
      req.setTargetInstance(topNameInstanceMap.get(key), useInnerClass);
    }
    
    return requirements;
  }
  
  public static BinaryConditionTerm elementDataLengthHack(BinaryConditionTerm binaryTerm) {
    BinaryConditionTerm ret = binaryTerm;
    
    Instance left  = binaryTerm.getInstance1();
    Instance right = binaryTerm.getInstance2();
    if (binaryTerm.getComparator() == Comparator.OP_EQUAL && right.isConstant()) {
      Reference ref = left.getLastReference();
      if (ref != null && ref.getName().equals("length") && right.getValue().startsWith("#!")) {
        String str = left.toString();
        if (str.endsWith(".elementData.length")) {
          Reference parent = ref.getDeclaringInstance().getLastReference()
                                .getDeclaringInstance().getLastReference();
          if (parent != null && (parent.getType().equals("Ljava/util/List") || 
                                 parent.getType().equals("Ljava/util/ArrayList") || 
                                 parent.getType().equals("Ljava/util/Vector"))) {
            if (right.getValue().startsWith("#!")) {
              right = new Instance("#!" + right.getValueWithoutPrefix() + "|#!10", "I", null);
              ret = new BinaryConditionTerm(left, binaryTerm.getComparator(), right);
            }
          }
          else if (parent == null) { // (v9999.allResults.__table__ @ #!0).elementData.length
            Instance arrayElem = ref.getDeclaringInstance().getLastReference().getDeclaringInstance(); 
            if (arrayElem != null && (arrayElem.getType().equals("Ljava/util/List") || 
                                      arrayElem.getType().equals("Ljava/util/ArrayList") || 
                                      arrayElem.getType().equals("Ljava/util/Vector")))  {
              if (right.getValue().startsWith("#!")) {
                right = new Instance("#!" + right.getValueWithoutPrefix() + "|#!10", "I", null);
                ret = new BinaryConditionTerm(left, binaryTerm.getComparator(), right);
              }
            }
          }
        }
      }
    }
    return ret;
  }
  
  private static final Pattern s_pattern1 = Pattern.compile(
      "^(v[0-9]+(?:(?:\\[[\\#\\!]*[0-9]+\\])*\\.[\\w_\\$]+(?:\\[[\\#\\!]*[0-9]+\\])*)*) == " +
      "((?:(?:[\\#\\!]*[\\-0-9]+[\\|]*)+)|(?:(?:\\#\\#[\\S]*)+))$"); // v1/v1.value/v1.value.next/v1.value[#!1] == #!21474836471/v1.str == ##str
  private static final Pattern s_pattern2 = Pattern.compile(
      "^(L[\\w_\\$/]+(?:\\.[\\w_\\$]+(?:\\[[\\#\\!]*[0-9]+\\])*)*) == " +
      "((?:(?:[\\#\\!]*[\\-0-9]+[\\|]*)+)|(?:(?:\\#\\#[\\S]*)+))$"); // Lorg/apache/log4j/NDC.ht == #!21474836471; Lorg/apache/log4j/NDC.ht[#!1] == #!21474836471, Lorg/apache/log4j/NDC.str == ##str 
  private static void parseFieldAccess(String modelLine, IR ir, Hashtable<String, List<Instance>> modelInstanceMap, 
      Hashtable<String, Instance> nameInstanceMap, Hashtable<Instance, String> instanceNameMap,  
      Hashtable<Instance, String> instanceModelMap, Hashtable<String, Instance> topInstances) {

    try {
      Matcher matcher = null;
      Pattern pattern = modelLine.startsWith("L") ? s_pattern2 : s_pattern1;
      
      if ((matcher = pattern.matcher(modelLine)).find()) {
        String left  = matcher.group(1);
        String right = matcher.group(2);
        
        String[] fieldNames = left.split("\\.");
        String varName = fieldNames[0];
        varName = varName.endsWith("]") ? varName.substring(0, varName.indexOf('[')) : varName; // e.g, v1[0]

        // create instance1 and its declaring instances
        Instance currentInstance = null;
        String currentName = "";
        for (int i = 0; i < fieldNames.length; i++) {
          String fieldName = fieldNames[i];
          String indexStr = null;
          if (fieldName.endsWith("]")) { // e.g, field[0]
            int index = fieldName.indexOf('[');
            indexStr  = fieldName.substring(index + 1, fieldName.length() - 1);
            fieldName = fieldName.substring(0, index);
          }
          currentName += (currentName.length() > 0 ? "." : "") + fieldName;
          
          Instance instance = nameInstanceMap.get(currentName); // the declaring instance may have already been created
          if (instance == null) {
            if (i == 0) { // top instance
              currentInstance = new Instance("", null);
              if (varName.startsWith("L")) { // Lorg/apache/log4j/NDC
                new Reference(varName, varName, "", currentInstance, null, true);
              }
              else { // v1
                String varType = ir.getParameterType(Integer.parseInt(varName.substring(1)) - 1).getName().toString();
                new Reference("v9999", varType, "", currentInstance, null, true);
              }
              topInstances.put(varName, currentInstance);
            }
            else {
              Instance fieldInstance = new Instance("", null);
              currentInstance.setField(fieldName, "Unknown-Type", "", fieldInstance, true, true);
              currentInstance = fieldInstance;
            }
            nameInstanceMap.put(currentName, currentInstance);
            instanceNameMap.put(currentInstance, currentName);
          }
          else {
            currentInstance = instance;
          }
          
          if (indexStr != null) {
            currentName = currentName + "[" + indexStr + "]";

            Instance arrayInstance = nameInstanceMap.get(currentName);
            if (arrayInstance == null) {
              arrayInstance = new Instance(currentInstance, INSTANCE_OP.DUMMY, new Instance(indexStr, "I", null), null);
              nameInstanceMap.put(currentName, arrayInstance);
              instanceNameMap.put(arrayInstance, currentName);
            }
            currentInstance = arrayInstance;
          }
        }
        
        // save instance and model value mapping
        List<Instance> instances = modelInstanceMap.get(right);
        if (instances == null) {
          instances = new ArrayList<Instance>();
          modelInstanceMap.put(right, instances);
        }
        instances.add(currentInstance);
        instanceModelMap.put(currentInstance, right);
      }
      else {
        System.err.println("Unable to analyze model line: " + modelLine);
      }
    } catch (Exception e) {
      System.err.println("Unable to analyze model line: " + modelLine);
    }
  }
  
  // parse a field model term and create the corresponding BinaryConditionTerm. 
  // Explicit types are also assigned to target instances here.
  private static BinaryConditionTerm parseFieldModelTerm(WalaAnalyzer walaAnalyzer, String modelLine, IR ir, 
      Hashtable<String, String> nameExplicitTypeMap, Hashtable<String, List<Instance>> modelInstanceMap, 
      Hashtable<String, Instance> nameInstanceMap, Hashtable<Instance, String> instanceModelMap) {
    BinaryConditionTerm binaryTerm = null;
    
    try {
      Matcher matcher = null;
      Pattern pattern = modelLine.startsWith("L") ? s_pattern2 : s_pattern1;

      if ((matcher = pattern.matcher(modelLine)).find()) {
        String left  = matcher.group(1);
        String right = matcher.group(2);
        
        String[] fieldNames = left.split("\\.");
        String varName = fieldNames[0];
        varName = varName.endsWith("]") ? varName.substring(0, varName.indexOf('[')) : varName; // e.g, v1[0]

        // create instance1
        Instance currentInstance = null;
        String currentType = null;
        String currentName = "";
        for (int i = 0; i < fieldNames.length; i++) {
          String fieldName = fieldNames[i];
          String indexStr = null;
          if (fieldName.endsWith("]")) { // e.g, field[0]
            int index = fieldName.indexOf('[');
            indexStr  = fieldName.substring(index + 1, fieldName.length() - 1);
            fieldName = fieldName.substring(0, index);
          }
          currentName += (currentName.length() > 0 ? "." : "") + fieldName;
          
          currentInstance = nameInstanceMap.get(currentName); // all instances have been parsed previously
          if (i == 0) { // top instance
            currentType = varName.startsWith("L") ? varName : 
              ir.getParameterType(Integer.parseInt(varName.substring(1)) - 1).getName().toString();
          }
          else {
            String fieldType = WalaUtils.findFieldType(walaAnalyzer, currentType, fieldName);
            currentType = fieldType.equals("Unknown-Type") ? pseudoImplTypes(currentType, fieldName) : fieldType;
          }

          // find explicit type information and set type
          String explicitType = nameExplicitTypeMap.get(currentName);
          if (explicitType != null && (currentType.equals("Unknown-Type") || 
                                       Utils.canCastTo(currentType, explicitType) /* more specific */ )) {
            currentType = explicitType;
          }
          currentInstance.getLastReference().setType(currentType);

          // if is array instance
          if (indexStr != null) {
            String modelValue = instanceModelMap.get(currentInstance);
            String arrayInstanceName = "(" + modelValue + " @ " + indexStr + ")";
            
            currentType = currentType.startsWith("[") ? currentType.substring(1) : "Unknown-Type";
            explicitType = nameExplicitTypeMap.get(arrayInstanceName);
            if (explicitType != null && (currentType.equals("Unknown-Type") || 
                                         Utils.canCastTo(currentType, explicitType) /* more specific */)) {
              currentType = explicitType;
            }

            // all instances have been parsed previously
            currentName = currentName + "[" + indexStr + "]";
            Instance arrayInstance = nameInstanceMap.get(currentName);
            arrayInstance.setType(currentType);
            currentInstance = arrayInstance;
          }
        }
        
        // create binary term
        Instance rightInstance = new Instance(right, currentType, null);
        Comparator comp = Comparator.OP_EQUAL;
        if (right.startsWith("#!")) {
          if (right.equals("#!21474836471")) {
            rightInstance = new Instance("null", currentType, null);
          }
          else if (!Utils.isPrimitiveType(currentType)) { // e.g., #!2147483649 -> notnull
            rightInstance = new Instance("null", currentType, null);
            comp = Comparator.OP_INEQUAL;
          }
          else if (currentType.equals("Z")) { // all non-0 booleans are casted to 1
            if (!rightInstance.getValueWithoutPrefix().equals("0")) {
              rightInstance = new Instance("#!1", currentType, null);
            }
          }
        }
        binaryTerm = new BinaryConditionTerm(currentInstance, comp, rightInstance);

        // ArrayList/Vector.elementData.length hack: Since solver only outputs one model, 
        // thus limiting the elementData.length field to a particular value. However, in 
        // reality, elementData.length can always be handled properly by ArrayList/Vector, 
        // thus, we manual set the value to 10 so that the simple constructor can be used.
        binaryTerm = elementDataLengthHack(binaryTerm);
      }
      else {
        System.err.println("Unable to analyze model line: " + modelLine);
      }
    } catch (Exception e) {
      System.err.println("Unable to analyze model line: " + modelLine);
    }
    return binaryTerm;
  }

  public static String pseudoImplTypes(String objType, String fieldName) {
    String fieldType = "Unknown-Type";
    
    // String2, in JDK7, String does not have count and offset field anymore
    if (objType.equals("Ljava/lang/String") && (fieldName.equals("count") || fieldName.equals("offset"))) {
      fieldType = "I";
    }
    else if (fieldName.equals("size") || fieldName.equals("count") || fieldName.equals("current")) {
      fieldType = "I";
    }
    else if (objType.startsWith("[") && fieldName.equals("length")) {
      fieldType = "I";
    }
    else if (fieldName.equals("__table__")) {
      fieldType = "[Ljava/lang/Object";
    }
    else if (fieldName.equals("__hashcode__")) {
      fieldType = "I";
    }
    else if ((objType.matches("L[\\S]+Map") || 
              objType.matches("Ljava/util/Hashtable")) && fieldName.equals("size")) {
      fieldType = "I";
    }
    else if (fieldName.equals("elementData")) {
      fieldType = "[Ljava/lang/Object";
    }
    
    return fieldType;
  }
  
  // return a list of terms because e.g. in (#!104306348577 @ #!0) == #!49085340507
  // #!104306348577 may correspond to multiple instances
  private static final Pattern s_pattern3 = Pattern.compile(
      "^\\(([\\#\\!]*[0-9]+) @ ([\\#\\!]*[0-9]+)\\) == ((?:(?:[\\#\\!]*[\\-0-9]+[\\|]*)+)|(?:(?:\\#\\#[\\S]*)+))$"); // (#!16642998279 @ #!0) == #!2147483649, (#!16642998279 @ #!0) == ##str
  private static List<BinaryConditionTerm> parseArrayModelTerm(String modelLine, Hashtable<String, String> nameExplicitTypeMap, 
      Hashtable<String, Instance> nameInstanceMap, Hashtable<Instance, String> instanceNameMap, 
      Hashtable<String, List<Instance>> modelInstanceMap, Hashtable<Instance, String> instanceModelMap) {
    List<BinaryConditionTerm> terms = new ArrayList<BinaryConditionTerm>();
    
    Matcher matcher = null;
    if ((matcher = s_pattern3.matcher(modelLine)).find()) {
      String left  = matcher.group(1);
      String index = matcher.group(2);
      String right = matcher.group(3);

      // making an assumption that, left can only be non-array element
      List<Instance> instances = modelInstanceMap.get(left);
      if (instances != null) {
        // if there are more than one instance matching this model 
        // value, we have no choice but to use them all
        for (int i = 0, size = instances.size(); i < size; i++) {
          Instance instance = instances.get(i);
          
          // make sure instance is an array
          if ((instance.getLastReference() == null || !instance.getLastRefType().startsWith("[")) && 
              (instance.getType() == null || !instance.getType().startsWith("["))) {
            continue;
          }
          
          // obtain type
          String elemType       = null;
          Instance elemInstance = null;
          
          String instanceName = instanceNameMap.get(instance);
          elemInstance = nameInstanceMap.get(instanceName + "[" + index + "]");
          if (elemInstance != null) {
            elemType = elemInstance.getType() != null ? elemInstance.getType() : "Unknown-Type";
          }
          else { // not found, create it
            Instance arrayInstance = instance;
            if (instance.getLastReference() != null && instance.getLastRefType().startsWith("[")) {
              elemType = instance.getLastRefType().substring(1);
            }
            else {
              elemType = instance.getType().substring(1);
            }
            
            // this is how we represent instance[index]: (arrayRefInstance @ indexInstance)
            Instance indexInstance = new Instance(index, "I", null);
            elemInstance = new Instance(arrayInstance, INSTANCE_OP.DUMMY, indexInstance, null);
          } 
    
          // obtain explicit type information
          String explicitType = nameExplicitTypeMap.get("(" + left + " @ " + index + ")");
          if (explicitType != null && (elemType.equals("Unknown-Type") || 
                                       Utils.canCastTo(elemType, explicitType) /* more specific */)) {
            elemType = explicitType;
          }
          // for a (arrayRefInstance @ indexInstance) type instance, 
          // we set type to it directly as it does not have Reference
          elemInstance.setType(elemType);
          
          // create binary term
          Instance rightInstance = new Instance(right, elemType, null);
          Comparator comp = Comparator.OP_EQUAL;
          if (right.startsWith("#!")) {
            if (right.equals("#!21474836471")) {
              rightInstance = new Instance("null", elemType, null);
            }
            else if (!Utils.isPrimitiveType(elemType)) { // e.g., #!2147483649 -> notnull
              rightInstance = new Instance("null", elemType, null);
              comp = Comparator.OP_INEQUAL;
            }
          }
          terms.add(new BinaryConditionTerm(elemInstance, comp, rightInstance));
        }
      }
      else {
        System.err.println("Cannot find instancce with model value: " + left);
      }
    }
    else {
      System.err.println("Unable to analyze model line: " + modelLine);
    }
    
    return terms;
  }

  private static void addToRequirements(Requirements requirements, Condition condition, 
      Hashtable<String, Instance> topNameInstanceMap) {
    
    // get varName (topInstance's name is already v9999, we want the actual v1/v2, etc)
    String varName = null;
    
    HashSet<Instance> topInstances = condition.getRelatedTopInstances(new Hashtable<String, Relation>());
    Instance topInstance = topInstances.iterator().next(); // should have exactly one
    
    // match variable name
    Enumeration<String> keys = topNameInstanceMap.keys();
    while (keys.hasMoreElements() && varName == null) {
      String key = (String) keys.nextElement();
      varName = (topNameInstanceMap.get(key) == topInstance) ? key : null;
    }
    
    // save the requirement term
    Requirement req = requirements.getRequirement(varName);
    if (req == null) {
      req = new Requirement(varName);
      requirements.addRequirement(varName, req);
    }
    req.addCondition(condition);
  }
  
  // v1 instanceOf(Lorg/apache/tools/ant/util/DOMElementWriter) == #!1
  private static void handleInstanceOf(String modelLine, Hashtable<String, String> nameTypeMap) {
    int index1 = modelLine.indexOf(" instanceOf(");
    int index2 = modelLine.indexOf(") == ");
    String instanceName = modelLine.substring(0, index1);
    String typeName     = modelLine.substring(index1 + 12, index2);
    nameTypeMap.put(instanceName, typeName);
  }
  
  // v1 instanceof Lorg/apache/tools/ant/util/DOMElementWriter
  private static void handleInstanceof(String modelLine, Hashtable<String, String> nameTypeMap) {
    int index = modelLine.indexOf(" instanceof ");
    String instanceName = modelLine.substring(0, index);
    String typeName     = modelLine.substring(index + 12);
    nameTypeMap.put(instanceName, typeName);
  }
  
  private final Hashtable<String, Requirement> m_reqsMap;
  private List<String> m_ensureGenOrder;
}
