package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.Wala.WalaAnalyzer;
import hk.ust.cse.util.Utils;

import java.lang.reflect.Modifier;
import java.util.Collection;
import java.util.Set;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.types.TypeReference;

public class ExtendClassUtils {
  
  public static String extendClass(WalaAnalyzer walaAnalyzer, IClass toExtendClass, Set<IR> methodsToExpose) {
    StringBuilder classContent = new StringBuilder();
    
    // we cannot extend a final class
    if (!Modifier.isFinal(toExtendClass.getModifiers())) {
      // class header
      String classJavaName = Utils.getClassTypeJavaStr(toExtendClass.getName().toString());
      String classSimpleName = classJavaName.substring(classJavaName.lastIndexOf('.') + 1);
      classContent.append("  private static class ").append(classSimpleName)
                  .append(toExtendClass.isInterface() ? " implements " : " extends ")
                  .append(classJavaName).append(" {\n");
      
      // implement all constructors
      classContent.append(implConstructors(toExtendClass));
      classContent.append("\n");

      // implement all abstract methods
      classContent.append(implAbstractMethods(toExtendClass));
      
      // expose all necessary methods
      for (IR ir : methodsToExpose) {
        if (ir != null && !ir.getMethod().getName().toString().equals("<init>") /* constructors already implemented */ && 
           !ir.getMethod().isFinal()) {
          classContent.append(implMethod(ir.getMethod())).append("\n");
        }
      }
      
      // class closer
      classContent.append("  }\n");
    }
    
    return classContent.toString();
  }
  
  public static String encloseClass(String topClass, String innerClass) {
    StringBuilder classContent = new StringBuilder();
    
    int index = topClass.indexOf('\n');
    classContent.append(topClass.substring(0, index + 1));
    
    // append each line, add some indentation
    String[] lines = innerClass.split("\n");
    for (String line : lines) {
      classContent.append("  ").append(line).append("\n");
    }
    classContent.append("\n").append(topClass.substring(index + 1));
    return classContent.toString();
  }
  
  private static String implAbstractMethods(IClass toExtendClass) {
    StringBuilder implContent = new StringBuilder();
    
    // find all abstract methods
    Collection<IMethod> methods = toExtendClass.getDeclaredMethods();
    for (IMethod method : methods) {
      if (method.isAbstract()) {
        implContent.append(implMethod(method)).append("\n");
      }
    }
    
    return implContent.toString();
  }
  
  // implement an abstract method or expose a protected/default method
  private static String implMethod(IMethod method) {
    StringBuilder implContent = new StringBuilder();

    String methodName     = method.getName().toString();
    String retType        = method.getReturnType().getName().toString();
    String retTypeJavaStr = Utils.getClassTypeJavaStr(retType);
    
    // method header
    implContent.append("    public ").append(retTypeJavaStr).append(" ").append(methodName).append("(");
    for (int i = method.isStatic() ? 0 : 1, size = method.getNumberOfParameters(); i < size; i++) {
      String paramType = Utils.getClassTypeJavaStr(method.getParameterType(i).getName().toString());
      implContent.append(paramType).append(" ").append("v" + i);
      if (i != size - 1) {
        implContent.append(", ");
      }
    }
    implContent.append(")");
    
    // append throw exceptions
    TypeReference[] exceptions = null;
    try {
      exceptions = method.getDeclaredExceptions();
    } catch (Exception e) {}
    if (exceptions != null && exceptions.length > 0) {
      implContent.append(" throws ");
      for (int i = 0; i < exceptions.length; i++) {
        implContent.append(Utils.getClassTypeJavaStr(exceptions[i].getName().toString()));
        if (i != exceptions.length - 1) {
          implContent.append(", ");
        }
      }
    }
    implContent.append(" {\n");
    
    // method body
    if (method.isAbstract()) { // we want to implement it
      if (!retType.equals("V")) {
        implContent.append("      return ");
        if (Utils.isPrimitiveType(retType)) {
          implContent.append(Utils.getTypeDefaultValue(retType));
        }
        else {
          implContent.append("null");
        }
        implContent.append(";\n");
      }
    }
    else { // we want to expose it
      implContent.append("      ");
      if (!retType.equals("V")) {
        implContent.append("return ");
      }
      implContent.append("super.").append(methodName).append("(");
      for (int i = method.isStatic() ? 0 : 1, size = method.getNumberOfParameters(); i < size; i++) {
        implContent.append("v" + i);
        if (i != size - 1) {
          implContent.append(", ");
        }
      }
      implContent.append(");\n");
    }
    implContent.append("    }\n");
    
    return implContent.toString();
  }
  
  private static String implConstructors(IClass toExtendClass) {
    StringBuilder implContent = new StringBuilder();
    
    String classJavaName   = Utils.getClassTypeJavaStr(toExtendClass.getName().toString());
    String classSimpleName = classJavaName.substring(classJavaName.lastIndexOf('.') + 1);

    // find all non-private constructors
    for (IMethod method : toExtendClass.getDeclaredMethods()) {
      if (!method.isPrivate() && !method.isAbstract() && method.getName().toString().equals("<init>")) {
        // method header
        implContent.append("    public ").append(classSimpleName).append("(");
        for (int i = 1, size = method.getNumberOfParameters(); i < size; i++) {
          String paramType = Utils.getClassTypeJavaStr(method.getParameterType(i).getName().toString());
          implContent.append(paramType).append(" ").append("v" + i);
          if (i != size - 1) {
            implContent.append(", ");
          }
        }
        implContent.append(")");

        // append throw exceptions
        TypeReference[] exceptions = null;
        try {
          exceptions = method.getDeclaredExceptions();
        } catch (Exception e) {}
        if (exceptions != null && exceptions.length > 0) {
          implContent.append(" throws ");
          for (int i = 0; i < exceptions.length; i++) {
            implContent.append(Utils.getClassTypeJavaStr(exceptions[i].getName().toString()));
            if (i != exceptions.length - 1) {
              implContent.append(", ");
            }
          }
        }
        implContent.append(" {");
        
        // method body
        implContent.append("super(");
        for (int i = 1, size = method.getNumberOfParameters(); i < size; i++) {
          implContent.append("v" + i);
          if (i != size - 1) {
            implContent.append(", ");
          }
        }
        implContent.append(");}\n");
      }
    }
    
    return implContent.toString();
  }
}
