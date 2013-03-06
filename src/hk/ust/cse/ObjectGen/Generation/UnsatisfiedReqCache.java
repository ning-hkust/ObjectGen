package hk.ust.cse.ObjectGen.Generation;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class UnsatisfiedReqCache {

  public UnsatisfiedReqCache() {
    m_unsatCahce = new Hashtable<Integer, List<Requirement>>();
  }
  
  public boolean isAlreadyUnsat(Requirement reqToCheck, int currentStep) {
    boolean unsat = false;
    
    for (int i = currentStep; i >= 0 && !unsat; i--) {
      List<Requirement> unsatReqs = m_unsatCahce.get(i);
      if (unsatReqs != null) {
        for (int j = 0, size = unsatReqs.size(); j < size && !unsat; j++) {
          unsat = reqToCheck.subsumes(unsatReqs.get(j));
        }
      }
    }
    
    return unsat;
  }
  
  public void saveUnsatReq(Requirement unsatisfiable, int currentStep) {
    List<Requirement> unsatReqs = m_unsatCahce.get(currentStep);
    if (unsatReqs == null) {
      unsatReqs = new ArrayList<Requirement>();
      m_unsatCahce.put(currentStep, unsatReqs);
    }
    
    // if a weaker requirement is already unsatisfiable, no need to save the new one
    boolean toAdd = true;
    for (int i = 0, size = unsatReqs.size(); i < size && toAdd; i++) {
      toAdd = !unsatisfiable.subsumes(unsatReqs.get(i));
    }
    
    if (toAdd) {
      unsatReqs.add(unsatisfiable);
    }
  }
  
  private final Hashtable<Integer, List<Requirement>> m_unsatCahce;
}
