package hk.ust.cse.ObjectGen.Generation.TestCase;

import hk.ust.cse.ObjectGen.Generation.VarNamePool;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public abstract class Statement {
   
  public Statement() {
    m_variables = new ArrayList<Variable>();
  }
  
  public List<Variable> getVariables() {
    return m_variables;
  }
  
  public abstract Statement cloneWithNewNames(VarNamePool varNamePool, Hashtable<String, String> clonedVarMap);
  
  protected List<Variable> cloneVarsWithNewNames(VarNamePool varNamePool, Hashtable<String, String> clonedVarMap) {
    List<Variable> clonedVariables = new ArrayList<Variable>();
    
    for (Variable var : m_variables) {
      Variable clonedVar = null;
      if (var != null) {
        String varName = var.getVarName();
        if (varName.matches("v[0-9]+\\[[0-9]+\\]")) { // e.g. v6[0]
          int index = varName.lastIndexOf('[');
          String arrayVarName = varName.substring(0, index);
          
          String clonedArrayVarName = clonedVarMap.get(arrayVarName);
          if (clonedArrayVarName == null) {
            clonedArrayVarName = arrayVarName.matches("v[0-9]+") ? varNamePool.nextVariableName() : varName;
            clonedVarMap.put(arrayVarName, clonedArrayVarName);
          }
          clonedVar = var.cloneWithNewName(clonedArrayVarName + varName.substring(index));
        }
        else {
          String clonedVarName = clonedVarMap.get(varName);
          if (clonedVarName == null) {
            clonedVarName = varName.matches("v[0-9]+") ? varNamePool.nextVariableName() : varName;
            clonedVarMap.put(varName, clonedVarName);
          }
          clonedVar = var.cloneWithNewName(clonedVarName);
        }
      }
      clonedVariables.add(clonedVar);
    }
    return clonedVariables;
  }
  
  public static String visibleClassName(String className) {
    String visible = className;
    
    Class<?> clazz = Utils.findClass(className);
    if (clazz != null) {
      if (Modifier.isProtected(clazz.getModifiers()) || 
          Modifier.isPrivate(clazz.getModifiers()) || 
          Utils.isAnonymousClass(clazz)) {
        
        // find public parent class
        Class<?> superClass = Utils.getClosestPublicSuperClass(clazz);
        if (superClass != null && superClass != java.lang.Object.class) {
          visible = superClass.getName();
        }
        else {
          Class<?>[] interfaces = Utils.getPublicInterfaces(clazz);
          if (interfaces.length > 0) {
            visible = interfaces[0].getName();
          }
        }
      }
    }

    return Utils.getClassTypeJavaStr(visible);
  }
  
  protected final List<Variable> m_variables;
}
