package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;

import java.util.List;

public abstract class AbstractMethodSelector {

  protected AbstractMethodSelector() {
  }
  
  public abstract List<String> select(Requirement req);
}
