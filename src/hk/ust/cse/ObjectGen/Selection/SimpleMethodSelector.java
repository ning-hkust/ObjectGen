package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;

import java.util.ArrayList;
import java.util.List;

public class SimpleMethodSelector extends AbstractMethodSelector {

  public SimpleMethodSelector() {
    super();
  }
  
  public List<String> select(Requirement req) {
    List<String> methods = new ArrayList<String>();
    //methods.add("hk.ust.cse.ObjectGen.TestCases.TestObjectGen.add()V");
    methods.add("hk.ust.cse.ObjectGen.TestCases.TestObjectGen.add(Ljava/lang/String;)V");
    methods.add("hk.ust.cse.ObjectGen.TestCases.TestObjectGen.<init>()V");
    methods.add("hk.ust.cse.ObjectGen.TestCases.TestObjectGen.remove()V");
    methods.add("hk.ust.cse.ObjectGen.TestCases.TestObjectGen.print()V");
    return methods;
  }
}
