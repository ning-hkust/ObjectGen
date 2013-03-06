package hk.ust.cse.ObjectGen.TestCases;

public class TestObjectGen extends AbstractTestObjectGen {

  public TestObjectGen() {
    size = 0;
  }

  public void add(String s) {
    size += 1;
  }
  
  public int get() {
    return size;
  }
  
  public void remove() {
    size -= 1;
  }
  
//  public void setList() {
//    list = new Object[2];
//  }
  
  public void setList2() {
    list = new Object[2];
    if (list[0] == null) {
      list[1] = new Object();
    }
  }
  
//  public void setList3(Object[] objs) {
//    list = objs;
//  }
  
  public void useAbstract(AbstractTestObjectGen obj) {
    size = obj.get();
  }
  
//  public void print() {
//    if (size > 0) {
//      int a = 1;
//      //System.out.println("aa");
//    }
//    else {
//      //System.out.println("bb");
//    }
//  }
  

//  
//  // obj.list.length == 2
//  public static void main2(String[] args) throws Exception {
//    Reference target = new Reference("v9999", "Lhk/ust/cse/ObjectGen/TestCases/TestObjectGen", "", new Instance("", null), null, true);
//    Instance instance2 = new Instance("#!2", "I", null);
//    target.getInstance().setField("list", "[I", "", new Instance("", null), true, true);
//    Reference fieldRef = target.getInstance().getField("list");
//    fieldRef.getInstance().setField("length", "I", "", new Instance("", null), true, true);
//    fieldRef = fieldRef.getInstance().getField("length");
//    BinaryConditionTerm term = new BinaryConditionTerm(fieldRef.getInstance(), Comparator.OP_EQUAL, instance2);
//    Requirement req = new Requirement();
//    req.addRequirementTerm(term);
//    req.setTargetInstance(target.getInstance());
//    
//    Generator generator = new Generator("./hk.ust.cse.ObjectGen.jar", "./summaries/", 10, 5);
//    Sequence sequence = generator.generate(req, new int[]{0});
//    if (sequence != null) {
//      System.out.println(sequence.toString());
//    }
//    else {
//      System.err.println("Failed to generate sequence!");
//    }
//  }
  
  
  private Object[] list;
}
