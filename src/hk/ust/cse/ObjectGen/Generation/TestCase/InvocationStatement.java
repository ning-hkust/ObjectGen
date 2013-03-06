package hk.ust.cse.ObjectGen.Generation.TestCase;

import hk.ust.cse.ObjectGen.Generation.VarNamePool;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.Hashtable;
import java.util.List;

import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ssa.IR;


public class InvocationStatement extends Statement {

  public InvocationStatement(IR ir, List<Variable> parameters, Variable assignTo, boolean useInnerClass) {
    m_variables.addAll(parameters);
    m_ir            = ir;
    m_assignTo      = assignTo;
    m_useInnerClass = useInnerClass;
  }
  
  public IR getMethod() {
    return m_ir;
  }
  
  public Variable getAssignTo() {
    return m_assignTo;
  }
  
  public String toString() {
    StringBuilder str = new StringBuilder("    ");
    
    IMethod method = m_ir.getMethod();
    String declClassType     = method.getDeclaringClass().getName().toString();
    String declClassJavaType = Utils.getClassTypeJavaStr(declClassType);

    if (method.isStatic()) {
      if (m_assignTo != null) {
        String className = m_assignTo.getClassName();
        String visibleName = className != null ? visibleClassName(className) : className;
        str.append(visibleName).append(" ").append(m_assignTo.getVarName())
           .append(" = (").append(visibleName).append(") ");
      }
      str.append(declClassJavaType).append(".").append(method.getName().toString()).append("(");
    }
    else if (method.getName().toString().equals("<init>")) {
      String typeName = declClassJavaType;
      if (m_useInnerClass) {
        // Lorg/apache/commons/collections/bidimap/AbstractDualBidiMap$EntrySetIterator
        typeName = declClassType.substring(declClassType.lastIndexOf('/') + 1);
        typeName = typeName.replace('$', '.');
      }
      str.append(typeName).append(" ").append(m_variables.get(0).getVarName());
      str.append(" = new ").append(typeName).append("(");
    }
    else {
      if (m_assignTo != null) {
        String typeName = m_assignTo.getClassName();
        if (m_useInnerClass) {
          // Lorg/apache/commons/collections/bidimap/AbstractDualBidiMap$EntrySetIterator
          typeName = typeName.substring(typeName.lastIndexOf('/') + 1);
          typeName = typeName.replace('$', '.');
        }
        else {
          typeName = typeName != null ? visibleClassName(typeName) : typeName;
        }
        str.append(typeName).append(" ").append(m_assignTo.getVarName())
           .append(" = (").append(typeName).append(") ");
      }
      
      // avoid null dereference
      String caller = m_variables.get(0).getVarName();
      str.append(caller.equals("null") ? "// " : "").append(caller);
      str.append(".").append(method.getName().toString()).append("(");
    }
    
    // append parameters
    for (int i = method.isStatic() ? 0 : 1, size = m_variables.size(); i < size; i++) {
      String paramName = null;
      String paramType = m_ir.getParameterType(i).getName().toString();
      Variable parameter = m_variables.get(i);
      if (parameter == null) {
        paramName = Utils.getTypeRandomValue(paramType.equals("J") ? "I" : paramType);
        paramName = paramType.equals("C") ? "'" + paramName + "'" : paramName;
      }
      else {
        paramName = parameter.getVarName();
      }
      
      if (Utils.isPrimitiveType(paramType)) {
        paramType = Utils.getClassTypeJavaStr(paramType);
        str.append("(").append(paramType).append(") ");
      }
      else {
        Class<?> cls = Utils.findClass(paramType);
        if (cls != null && Modifier.isPublic(cls.getModifiers())) {
          paramType = Utils.getClassTypeJavaStr(paramType);
          str.append("(").append(paramType).append(") ");
        }
      }
      str.append(paramName);
      if (i != size - 1) {
        str.append(", ");
      }
    }
    str.append(");");
    
    return str.toString();
  }
  
  @Override
  public Statement cloneWithNewNames(VarNamePool varNamePool, Hashtable<String, String> clonedVarMap) {
    List<Variable> clonedVariables = cloneVarsWithNewNames(varNamePool, clonedVarMap);
    
    Variable clonedAssignTo = null;
    if (m_assignTo != null) {
      String assignToVarName = clonedVarMap.get(m_assignTo.getVarName());
      if (assignToVarName == null) {
        assignToVarName = varNamePool.nextVariableName();
        clonedVarMap.put(m_assignTo.getVarName(), assignToVarName);
      }
      clonedAssignTo = m_assignTo.cloneWithNewName(assignToVarName);
    }
    
    return new InvocationStatement(m_ir, clonedVariables, clonedAssignTo, m_useInnerClass);
  }
  
  private final IR       m_ir;
  private final Variable m_assignTo;
  private final boolean  m_useInnerClass;
}
