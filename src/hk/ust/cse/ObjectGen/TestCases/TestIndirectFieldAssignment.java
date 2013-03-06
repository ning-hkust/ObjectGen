package hk.ust.cse.ObjectGen.TestCases;

public class TestIndirectFieldAssignment {
  
  // effect should be: 1) obj: obj.field1 = 1, obj.field2 = 1; 2) obj: obj.field1 = -1, obj.field2 = 1 
  public static void test1(TestIndirectFieldAssignment obj) {
    obj.field1 = 0;
    obj.field2 = 1; // effect for field2 should be seen also
    // ret.invocation
    // replaced branch
    assignField1_1(obj);
    if (obj.field1 > 0) {
      obj.field1 = -1;
    }
  }
  
  // test for overrided field, and linkage
  // effect should be: obj: obj.field3 = obj.field4; obj.field3: obj.field3.field1 = 1
  public static void test2(TestIndirectFieldAssignment obj) {
    assignField3_1_1(obj);
    obj.field3 = obj.field4;
  }
  
  // test for multiple hidden v1 and assignment() in middle
  // effect should be: 1) obj: obj.field1 = 2; obj.field2 = 1; 2) obj: obj.field1 = -1; obj.field2 = 10;
  public static void test3(TestIndirectFieldAssignment obj) {
    obj.field1 = 0;
    assignField1_1(obj);
    obj.field1 = 10;
    obj.field2 = 1;
    assignField1_2(obj);
    if (obj.field1 > 0) {
      assignField2_10(obj);
      obj.field1 = -1;
    }
  }
  
  // test for if invocation effect can be merged to hidden instance as well
  // effect should be: 1) obj: obj.field4 = obj.field3; obj.field4.field1 = obj.field3.field1; obj.field3.field1 = 1
  // 2) obj: obj.field1 = 1; obj.field4 = obj.field3; obj.field4.field1 = obj.field3.field1; obj.field3.field1 = 1
  // in the path condition, it should be: obj.field3.field1 ==/!= #!1 instead of #!1 ==/!= #!1
  public static void test4(TestIndirectFieldAssignment obj) {
    obj.field4 = obj.field3;
    if (obj.field4.field1 == 1) { // should not be 1 == 1 since the assign() is later
      obj.field1 = 1;
    }
    assignField3_1_1(obj);
  }
  
  // test for multi-layer
  // effect should be: obj: obj.field1 = 1
  public static void test5(TestIndirectFieldAssignment obj) {
    assignField1_1_indirect(obj);
  }
  
  // test for merge field effect sequence
  // effect should be: obj1: obj1.field1 = 1; obj1.field2 = obj2.field2
  public static void test6(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field2 = obj2.field2;
    assignField1_1(obj1);
  }
  
  // test for translateScope
  // effect should be: obj2: obj2.field1 = (obj1.field1 + obj1.field2)
  public static void test7(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignFieldAdd(obj2, obj1);
  }
  
  // test for multiple level override
  // effect should be: obj1: obj1.field3 = obj3; obj1.field3: obj1.field3.field4 = obj2; obj1.field3.field4: obj1.field3.field4.field1 = 1
  public static void test8(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2, TestIndirectFieldAssignment obj3) {
    obj1.field3.field4.field1 = 1;
    obj1.field3.field4 = obj2;
    obj1.field3 = obj3;
  }
  
  // test for oldlist passing
  // effect should be: obj1: obj1.field3 = obj2; obj1.field3: obj1.field3.field1 = 1
  public static void test9(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignFieldOverride(obj1, obj2);
  }
  
  // test for multiple old instances
  // effect should be: obj1: obj1.field3 = obj1; obj1.field3: obj1.field3.field1 = 1; obj2: obj2.field1 = 2
  public static void test10(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignFieldOverride2(obj1, obj2);
  }
  
  //XXX
  // test for oldlist passing
  // effect should be: obj1: obj1.field1 = #!1 + #!1
  public static void test11(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignField1_1(obj1);
    obj1.field1 = obj1.field1 + obj1.field1;
    obj1.field1 = obj1.field1;
  }
  
  // test for oldlist passing
  // effect should be: obj1: obj1.field1 = 2; obj1.field2 = 2;
  public static void test12(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignField1_1_2(obj1);
    obj1.field2 = obj1.field1;
  }
  
  // test for passing parameter
  // effect should be: 1) obj1: obj1.field1 <= 0: obj1.field1 = 0; 2) obj1: obj1.field1 > 0: obj1.field1 = 1
  public static void test13(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field1 = assignField13(obj1.field1);
  }
  
  // test for passing parameter
  // effect should be: obj1: obj1.field1 = obj2.field2; 
  public static void test14(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    assignField14(obj1, obj2.field2);
  }
  
  // test for hidden transfer
  // effect should be: obj1: obj1.field1 = 1, obj1.field2 = 1; obj2: obj2.field1 = 1
  public static void test15(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj2.field1 = 1;
    obj1.field1 = obj2.field1;
    assignField2_10(obj1);
    obj1.field2 = obj1.field1;
  }

  // test for constant as argument
  // effect should be: obj1: obj1.field1 = 1, obj1.field3 = null
  public static void test16(TestIndirectFieldAssignment obj1) {
    assignField1(obj1, 1);
    assignField3(obj1, null);
  }
  
  //effect should be: obj1: obj1.field1 = obj1.field3.field1 + 1, obj1.field3.field1 = obj1.field3.field1 + 1; obj2: obj2.field1 = 1
  public static void test17(TestIndirectFieldAssignment obj1) {
    obj1.field1 = obj1.field3.field1 + 1;
    if (obj1.field3.field1 == 0) {
      obj1.field2 = 0;
    }
    obj1.field3 = obj1;
    if (obj1.field3.field1 == 1) {
      obj1.field2 = 1;
    }
  }
  
  public static void assignField1(TestIndirectFieldAssignment obj, int num) {
    obj.field1 = num;
  }
  
  public static void assignField3(TestIndirectFieldAssignment obj, TestIndirectFieldAssignment obj2) {
    obj.field3 = obj2;
  }
  
  public static void assignField1_1(TestIndirectFieldAssignment obj) {
    obj.field1 = 1;
  }
  
  public static void assignField1_1_2(TestIndirectFieldAssignment obj) {
    obj.field1 = 1;
    obj.field1 = 2;
  }
  
  public static void assignField1_1_indirect(TestIndirectFieldAssignment obj) {
    assignField1_1(obj);
  }

  public static void assignField1_2(TestIndirectFieldAssignment obj) {
    obj.field1 = 2;
  }
  
  public static void assignField2_10(TestIndirectFieldAssignment obj) {
    obj.field2 = 10;
  }
  
  public static void assignField3_1_1(TestIndirectFieldAssignment obj) {
    obj.field3.field1 = 1;
  }
  
  public static int assignField13(int num) {
    if (num > 0) {
      return 1;
    }
    else {
      return 0;
    }
  }
  
  public static void assignField14(TestIndirectFieldAssignment obj1, int num) {
    obj1.field1 = num;
  }
  
  public static void assignFieldAdd(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field1 = obj2.field1 + obj2.field2;
  }
  
  public static void assignFieldOverride(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field3.field1 = 1;
    obj1.field3 = obj2;
  }
  
  public static void assignFieldOverride2(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field3.field1 = 1;
    obj1.field3 = obj2;
    obj1.field3.field1 = 2;
    obj1.field3 = obj1;
  }
  
  public static void assignFieldOverride3(TestIndirectFieldAssignment obj1, TestIndirectFieldAssignment obj2) {
    obj1.field3.field1 = 1;
    obj1.field3 = obj2;
    obj1.field3.field1 = 2;
    obj1.field3 = obj1;
  }

  private int field1;
  private int field2;
  private TestIndirectFieldAssignment field3;
  private TestIndirectFieldAssignment field4;
}
