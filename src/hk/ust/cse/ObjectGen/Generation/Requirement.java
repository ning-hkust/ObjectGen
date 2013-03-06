package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm;
import hk.ust.cse.Prevision.PathCondition.BinaryConditionTerm.Comparator;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.util.Utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

public class Requirement {

  public Requirement(String varName) {
    m_varName          = varName;
    m_requirementTerms = new ArrayList<BinaryConditionTerm>();
    m_compareStrings   = new HashSet<String>();
  }
  
  public void addRequirementTerm(BinaryConditionTerm term) {
    m_requirementTerms.add(term);
    m_compareStrings.add(toCompareString(term));
  }
  
  public BinaryConditionTerm getRequirementTerm(int index) {
    return m_requirementTerms.get(index);
  }
  
  public List<BinaryConditionTerm> getRequirementTerms() {
    return m_requirementTerms;
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
  
  public Class<?> getTargetType() {
    return m_targetType;
  }
  
  public String getTargetTypeDeclJavaName() {
    return m_targetTypeDeclJavaName;
  }
  
  public boolean getUseInnerClass() {
    return m_useInnerClass;
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
  
  private String toCompareString(BinaryConditionTerm term) {
    String compareStr = null;
    
    Instance instance1 = term.getInstance1();
    compareStr = term.toString();
    int index = compareStr.indexOf(term.getComparator().equals(Comparator.OP_EQUAL) ? " == " : " != ");
    compareStr = toCompareString(instance1) + compareStr.substring(index);
    
    if (instance1.getRight() == null) { // not function interpretation
      String value = term.getInstance2().getValue();
      if (!Utils.isPrimitiveType(instance1.getLastRefType()) && 
        term.getComparator().equals(Comparator.OP_INEQUAL) && value.equals("null")) {
        String typeName = instance1.getLastRefType();
        compareStr = compareStr.substring(0, compareStr.indexOf(" != ")) + " == " + typeName;
      }
    }
    else { // array access
      String value = term.getInstance2().getValue();
      String typeName = instance1.getLeft().getLastRefType();
      typeName = typeName.startsWith("[") ? typeName.substring(1) : typeName;
      if (!Utils.isPrimitiveType(typeName) && 
          term.getComparator().equals(Comparator.OP_INEQUAL) && value.equals("null")) {
        typeName = instance1.getType() != null ? instance1.getType() : typeName;
        compareStr = compareStr.substring(0, compareStr.indexOf(" != ")) + " == " + typeName;
      }
    }
    return compareStr;
  }
  
  private String toCompareString(Instance instance) {
    String compareStr = instance.toString();
    if (instance.getRight() == null) { // v1 or ??.field
      Instance topInstance = instance.getToppestInstance();
      if (topInstance.getRight() != null) { // (?? @ #!).field
        int index = compareStr.lastIndexOf(" @ ");
        compareStr = "(" + toCompareString(topInstance.getLeft()) + compareStr.substring(index);
      }
      else if (instance != topInstance) { // ??.field
        int index = compareStr.lastIndexOf(".");
        compareStr = toCompareString(topInstance) + compareStr.substring(index);
      }
      else { // v1
        compareStr = topInstance.getLastRefType();
      }
    }
    else { // (?? @ #!)
      int index = compareStr.lastIndexOf(" @ ");
      compareStr = "(" + toCompareString(instance.getLeft()) + compareStr.substring(index);
    }

    return compareStr;
  }
  
  private boolean                         m_useInnerClass;
  private Instance                        m_targetInstance;
  private Class<?>                        m_targetType;
  private String                          m_targetTypeDeclJavaName;
  private final String                    m_varName;
  private final List<BinaryConditionTerm> m_requirementTerms;
  private final HashSet<String>           m_compareStrings;
}
