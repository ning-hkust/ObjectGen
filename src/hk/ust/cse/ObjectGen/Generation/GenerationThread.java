package hk.ust.cse.ObjectGen.Generation;

import hk.ust.cse.ObjectGen.Generation.Generators.GenerationResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;

import java.util.Enumeration;


public class GenerationThread extends Thread {

  public void setRequirementsToGen(Requirements requirements, Generator generator, VarNamePool varNamePool) {
    m_requirements = requirements;
    m_generator    = generator;
    m_varNamePool  = varNamePool == null ? new VarNamePool() : varNamePool;
  }
  
  public void setStopFlag() {
    m_generator.setStopFlag();
  }
  
  public GenerationResult getLastGenResult() {
    return m_genResult;
  }
  
  public VarNamePool getLastVarNamePool() {
    return m_varNamePool;
  }
  
  public void run() {
    // clear result
    m_genResult = new GenerationResult();
    
    // supporting vars for generation
    HashCodeMap hashCodeVarMap = new HashCodeMap();
    
    // generate sequence for each parameter
    Enumeration<String> keys = m_requirements.keys();
    while (keys.hasMoreElements()) {
      String varName = (String) keys.nextElement();
      Requirement req = m_requirements.getRequirement(varName);

      HashCodeMap prevHashCodeVarMap = hashCodeVarMap.clone();
      Sequence sequence = m_generator.generate(req, m_varNamePool, hashCodeVarMap);
      if (sequence != null) {
        m_genResult.addSequence(varName, sequence);
      }
      else {
        m_genResult.addNotSat(varName);
        hashCodeVarMap = prevHashCodeVarMap;
      }
    }
  }
  
  private VarNamePool     m_varNamePool;
  private Generator       m_generator;
  private Requirements    m_requirements;

  private GenerationResult m_genResult;
}
