package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.Condition;
import hk.ust.cse.Prevision.PathCondition.ConditionTerm;
import hk.ust.cse.Prevision.PathCondition.TypeConditionTerm;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.util.Utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

public class Requirement {

  public Requirement(String varName) {
    m_varName        = varName;
    m_conditions     = new ArrayList<Condition>();
    m_compareStrings = new HashSet<String>();
  }
  
  public void addCondition(Condition condition) {
    m_conditions.add(condition);
    m_compareStrings.add(toCompareString(condition));
  }
  
  public Condition getCondition(int index) {
    return m_conditions.get(index);
  }
  
  public List<Condition> getConditions() {
    return m_conditions;
  }
  
  public HashSet<String> getCompareStrings() {
    return m_compareStrings;
  }
  
  public void setTargetInstance(Instance targetInstance, boolean useInnerClass) {
    m_targetInstance = targetInstance;
    m_useInnerClass  = useInnerClass;
    
    // get type first
    String typeName = m_targetInstance.getLastRefType();
    if (typeName != null) {
      m_targetType = Utils.findClass(typeName);
      m_targetTypeDeclJavaName = Utils.getClassTypeJavaStr(typeName);
      
//      // since m_targetTypeDeclJavaName is used as the declared type 
//      // for target in the source code, we cannot use private class
//      m_targetTypeDeclJavaName = Utils.getClassTypeJavaStr(typeName);
//      if (Modifier.isPrivate(m_targetType.getModifiers()) || Utils.isAnonymousClass(m_targetType)) {
//        Class<?> superClass = m_targetType.getSuperclass();
//        if (Modifier.isPublic(superClass.getModifiers()) && superClass != java.lang.Object.class) {
//          m_targetTypeDeclJavaName = superClass.getName();
//        }
//        else {
//          Class<?>[] interfaces = m_targetType.getInterfaces();
//          for (Class<?> anInterface : interfaces) {
//            if (Modifier.isPublic(anInterface.getModifiers())) {
//              m_targetTypeDeclJavaName = interfaces[0].getName();
//              break;
//            }
//          }
//        }
//      }
    }
    else {
      m_targetType             = null;
      m_targetTypeDeclJavaName = null;
    }
  }
  
  public void setTargetInstanceType(String typeName) {
    m_targetInstance.getLastReference().setType(typeName);
    setTargetInstance(m_targetInstance, m_useInnerClass);
  }
  
  public void setUseInnerClass(boolean useInnerClass) {
    m_useInnerClass = useInnerClass;
  }
  
  public Instance getTargetInstance() {
    return m_targetInstance;
  }
  
  public String getTargetInstanceName() {
    return m_targetInstance.toString();
  }
  
  public Class<?> getTargetType() {
    return m_targetType;
  }
  
  public String getTargetTypeDeclJavaName() {
    return m_targetTypeDeclJavaName;
  }
  
  public boolean getUseInnerClass() {
    return m_useInnerClass;
  }
  
  public boolean containsCondition(String conditionStr) {
    // ignore type conditions
    List<Condition> nonTypeConditions = new ArrayList<Condition>();
    for (Condition condition : m_conditions) {
      if (condition.getOnlyTypeTerm() == null) {
        nonTypeConditions.add(condition);
      }
    }

    boolean contains = false;
    for (int i = 0, size = nonTypeConditions.size(); i < size && !contains; i++) {
      BinaryConditionTerm term = nonTypeConditions.get(i).getOnlyBinaryTerm();
      String termStr = term != null ? term.toString() : null;
      contains = termStr != null && termStr.equals(conditionStr);
    }
    return contains;
  }
  
  // >=
  public boolean subsumes(Requirement req) {
    boolean subsumes = m_compareStrings.size() >= req.getCompareStrings().size();
    Iterator<String> iter = req.getCompareStrings().iterator();
    while (iter.hasNext() && subsumes) {
      subsumes = m_compareStrings.contains(iter.next());
    }
    return subsumes;
  }
  
  public int compareStringSize() {
    return m_compareStrings.size();
  }
  
  public String getVarName() {
    return m_varName;
  }
  
  public boolean hashCodeHackRelated() {
    boolean related = false;
    
    Iterator<String> iter = m_compareStrings.iterator();
    while (iter.hasNext() && !related) {
      String str = iter.next();
      related = str.contains("__table__") || str.contains("__hashcode__");
    }
    return related;
  }
  
  public int hashCode() {
    return m_compareStrings.size();
  }
  
  public boolean equals(Object o) {
    if (o == null) {
      return false;
    }
    
    if (!(o instanceof Requirement)) {
      return false;
    }
    
    Requirement req = (Requirement) o;
    boolean equal = req.getCompareStrings().size() == m_compareStrings.size();
    Iterator<String> iter = req.getCompareStrings().iterator();
    while (iter.hasNext() && equal) {
      equal = m_compareStrings.contains(iter.next());
    }
    return equal;
  }
  
  private String toCompareString(Condition condition) {
    StringBuilder compareStr = new StringBuilder();
    
    for (int i = 0, size = condition.getConditionTerms().size(); i < size; i++) {
      ConditionTerm term = condition.getConditionTerms().get(i);
      if (term instanceof BinaryConditionTerm) {
        compareStr.append(toCompareString((BinaryConditionTerm) term));
      }
      else if (term instanceof TypeConditionTerm) {
        compareStr.append(toCompareString((TypeConditionTerm) term));
      }
      if (i != size - 1) {
        compareStr.append(" or ");
      }
    }

    return compareStr.toString();
  }
  
  private String toCompareString(TypeConditionTerm term) {
    return toCompareString(term.getInstance1()) + " " + term.getComparator().toString() + " " + term.getTypeString();
  }
  
  private String toCompareString(BinaryConditionTerm term) {
    String compareStr = null;
    
    Instance instance1 = term.getInstance1();
    Instance instance2 = term.getInstance2();
    
    // convert ?? != null into ?? == typeName
    if (term.isNotEqualToNull()) {
      if (instance1.getRight() == null) { // not array access
        compareStr = toCompareString(instance1) + " == " + instance1.getLastRefType();
      }
      else { // array access
        String typeName = instance1.getLeft().getLastRefType();
        typeName = typeName.startsWith("[") ? typeName.substring(1) : typeName;
        typeName = instance1.getType() != null ? instance1.getType() : typeName;
        compareStr = toCompareString(instance1) + " == " + typeName;
      }
    }
    else {
      compareStr = toCompareString(instance1) + " " + term.getComparator().toString() + " " + toCompareString(instance2);
    }
    
    return compareStr;
  }
  
  private String toCompareString(Instance instance) {
    String compareStr = null;
    if (instance.getRight() == null) { // v1 or ??.field
      Instance topInstance = instance.getToppestInstance();
      if (instance != topInstance) { // v1.field or (?? @ ??).field
        compareStr = instance.toString();
        int index = compareStr.indexOf('.', compareStr.lastIndexOf(')') + 1);
        
        if (index >= 0) {
          compareStr = toCompareString(topInstance) + compareStr.substring(index);
        }
        else {
          // in case there is a method call string in summary path condition
          compareStr = toCompareString(topInstance) + compareStr.substring(topInstance.toString().length());
        }
      }
      else if (!instance.isConstant() && instance.getLastReference() != null) { // v1
        compareStr = topInstance.getLastRefType();
      }
      else {
        compareStr = instance.toString();
      }
    }
    else { // (?? @ ??)
      compareStr = "(" + toCompareString(instance.getLeft()) + " " + 
          instance.getOp() + " " + toCompareString(instance.getRight()) + ")";
    }

    return compareStr;
  }
  
  private boolean               m_useInnerClass;
  private Instance              m_targetInstance;
  private Class<?>              m_targetType;
  private String                m_targetTypeDeclJavaName;
  private final String          m_varName;
  private final List<Condition> m_conditions;
  private final HashSet<String> m_compareStrings;
}
