package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.Prevision.VirtualMachine.Instance;
import hk.ust.cse.Prevision.VirtualMachine.Reference;
import hk.ust.cse.Prevision_PseudoImpl.PseudoImplMap;
import hk.ust.cse.StaticAnalysis.SetFieldAnalyzer.SetFieldAnalyzer;
import hk.ust.cse.Wala.Jar2IR;
import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.LRUCache;
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

import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.types.TypeReference;

public class FieldMethodSelector extends AbstractMethodSelector {
  public FieldMethodSelector(WalaAnalyzer walaAnalyzer, boolean usePeudoImpl, int accessibility) {
    m_usePeudoImpl     = usePeudoImpl;
    m_setFieldAnalyzer = new SetFieldAnalyzer(walaAnalyzer, true, accessibility);
    
    // cache
    m_setFieldCache = new LRUCache(50);
  }
  
  public List<String> select(Requirement req) {
    List<String> methodSigs = new ArrayList<String>();
    
    // get target field names
    HashSet<String> fieldNames = new HashSet<String>();
    Instance topInstance = req.getTargetInstance();
    findRelatedFieldNames(topInstance, fieldNames, new HashSet<Instance>());

    String typeName = req.getTargetInstance().getLastRefType();
    Hashtable<String, List<Object[]>> setFields = findFieldSet(typeName);
    
    HashSet<Object[]> methodOrCtors = new HashSet<Object[]>();
    for (String fieldName : fieldNames) {
      List<Object[]> methodOrCtorsForField = setFields.get(fieldName);
      if (methodOrCtorsForField != null) {
        methodOrCtors.addAll(methodOrCtorsForField);
      }
    }
    
    // note that, the same method can have multiple depth as they 
    // can set different fields in different levels
    // sort by depth of any field
    List<Object[]> methodOrCtorsList = sortMethodOrCtors(methodOrCtors);
    
    // output the method signatures without redundancies
    HashSet<String> methodSigsAdded = new HashSet<String>();
    for (Object[] methodOrCtor : methodOrCtorsList) {
      IR ir = Jar2IR.getIR(m_setFieldAnalyzer.getWalaAnalyzer(), (Member) methodOrCtor[0]);
      IMethod method = ir.getMethod();
      Class<?> declClass = Utils.findClass(method.getDeclaringClass().getName().toString());
      
      String methodSig = method.getSignature();
      if (!methodSigsAdded.contains(methodSig) && !method.getName().toString().startsWith("access$") && 
          !(method.isProtected() && Modifier.isFinal(declClass.getModifiers())) && 
          !(method.isProtected() && isNotExtendableInner(declClass)) && 
          !hasAnonymousTypeParam(method) /* remove methods with anonymous inner class parameter type */) {
        methodSigs.add(methodSig);
        methodSigsAdded.add(methodSig);
      }
    }

    return methodSigs;
  }
  
  // why does it exist?
  private boolean hasAnonymousTypeParam(IMethod method) {
    boolean foundAnonymousParam = false;
    for (int i = method.isStatic() ? 0 : 1, size = method.getNumberOfParameters(); i < size && !foundAnonymousParam; i++) {
      TypeReference paramType = method.getParameterType(i);
      String typeName = paramType.getName().toString();
      int index = typeName.lastIndexOf('$');
      if (index >= 0) {
        try {
          Integer.parseInt(typeName.substring(index + 1));
          foundAnonymousParam = true;
        } catch (Exception e) {}
      }
    }
    return foundAnonymousParam;
  }
  
  private boolean isNotExtendableInner(Class<?> cls) {
    boolean ret = false;
    if (Utils.isInnerClass(cls)) {
      if (Modifier.isPrivate(cls.getModifiers())) {
        ret = true;
      }
      else {
        Class<?> outter = cls.getDeclaringClass();
        if (outter != null) {
          ret = Modifier.isPrivate(outter.getModifiers());
        }
      }
    }
    return ret;
  }
  
  // find related fields that need to be satisfy
  private void findRelatedFieldNames(Instance instance, HashSet<String> fieldNames, HashSet<Instance> visited) {
    if (visited.contains(instance)) {
      return;
    }
    visited.add(instance);
    
    if (!instance.isBounded()) {
      String declClass = instance.getLastRefType();
      String declClassJavaString = Utils.getClassTypeJavaStr(declClass);
      for (Reference fieldRef : instance.getFields()) {
        if (fieldRef.getName().contains(".")) {
          // due to bugs in summary extraction, there could be fields like: 
          // org.apache.commons.collections.Predicate.evaluate(Ljava/lang/Object;)Z_969578746583694
          continue;
        }
        
        if (fieldRef.getName().equals("__table__")) {
          fieldNames.add("hk.ust.cse.Prevision_PseudoImpl.Map.__table__");
          fieldNames.add("hk.ust.cse.Prevision_PseudoImpl.Table.__table__");
        }
        else {
          // find the exact class that declares the field
          Class<?> fieldDeclClass = Utils.getClosestFieldDeclClass(declClass, fieldRef.getName());
          String fullFieldString = (fieldDeclClass == null ? 
              declClassJavaString : fieldDeclClass.getName()) + "." + fieldRef.getName();
          fieldNames.add(fullFieldString);
          
          // also, this field name may have corresponding peudoImpl field name
          if (m_usePeudoImpl) {
            String peudoImplFieldName = PseudoImplMap.findPseudoImplFieldName(fullFieldString);
            if (peudoImplFieldName != null) {
              fieldNames.add(peudoImplFieldName);
            }
          }
          
          // find sub fields
          findRelatedFieldNames(fieldRef.getInstance(), fieldNames, visited);
        }
      }
    }
  }
  
  private List<Object[]> sortMethodOrCtors(HashSet<Object[]> methodOrCtors) {
    List<Object[]> methodOrCtorsList = new ArrayList<Object[]>(methodOrCtors);
    
    Collections.sort(methodOrCtorsList, new Comparator<Object[]>() {
      @Override
      public int compare(Object[] o1, Object[] o2) {
        if (((Integer) o1[1]).equals((Integer) o2[1])) {
          Member member1 = (Member) o1[0];
          Member member2 = (Member) o2[0];
          
          Class<?>[] params1 = (member1 instanceof Method) ? ((Method) member1).getParameterTypes() : 
                                                             ((Constructor<?>) member1).getParameterTypes();
          Class<?>[] params2 = (member2 instanceof Method) ? ((Method) member2).getParameterTypes() : 
                                                             ((Constructor<?>) member2).getParameterTypes();
          boolean allEasy1 = allEasyParams(params1);
          boolean allEasy2 = allEasyParams(params2);
          if ((allEasy1 && allEasy2) || (!allEasy1 && !allEasy2)) {
            return params1.length - params2.length;
          }
          else {
            return allEasy1 ? -1 : 1;
          }
        }
        else {
          return (Integer) o1[1] - (Integer) o2[1];
        }
      }
    });
    
    return methodOrCtorsList;
  }
  
  private boolean allEasyParams(Class<?>[] paramTypes) {
    boolean allEasy = true;
    for (int i = 0; i < paramTypes.length && allEasy; i++) {
      allEasy &= Utils.isPrimitiveType(paramTypes[i]);
    }
    return allEasy;
  }
  
  @SuppressWarnings("unchecked")
  public Hashtable<String, List<Object[]>> findFieldSet(String declClass) {
    Hashtable<String, List<Object[]>> setFields = null;
    
    setFields = (Hashtable<String, List<Object[]>>) m_setFieldCache.find(declClass);
    if (setFields == null) {
      setFields = m_setFieldAnalyzer.findAllSetFieldsWithDepth(declClass, 10, true, false);
      
      // save to cache
      m_setFieldCache.put(declClass, setFields);
    }
    
    return setFields;
  }

  private final boolean          m_usePeudoImpl;
  private final SetFieldAnalyzer m_setFieldAnalyzer;
  private final LRUCache         m_setFieldCache;
}
