package hk.ust.cse.ObjectGen.Selection;

import hk.ust.cse.ObjectGen.Generation.Requirement;
import hk.ust.cse.ObjectGen.Generation.Generators.ObjectGenerator;
import hk.ust.cse.ObjectGen.Generation.Generators.ParamReqDeductor.DeductResult;
import hk.ust.cse.ObjectGen.Generation.TestCase.Sequence;
import hk.ust.cse.ObjectGen.Summary.Summary;

import java.util.ArrayList;
import java.util.List;

import com.ibm.wala.ssa.IR;

public class SimpleSummarySelector extends AbstractSummarySelector {

  public SimpleSummarySelector(List<Summary> summaries, Requirement req, IR ir, ObjectGenerator objGenerator) {
    // obtain the immediate fields in req
    List<List<String>> targetFields = objGenerator.getTargetFields(req);
    
    m_summaries = new ArrayList<Summary>();
    for (Summary summary : summaries) {
      // check if this summary can potentially modify the target fields in req
      if (isSummaryUseful(summary, req, targetFields, ir) && 
         !isSummaryBadSize(summary, req, targetFields, ir)) {
        m_summaries.add(summary);
      }
    }
  }
  
  @Override
  public boolean hasNext() {
    return m_summaries.size() > 0;
  }
  
  @Override
  public Summary nextSummary(List<Requirement> prevSatReqs) {
    if (m_summaries.size() > 0) {
      return m_summaries.remove(0);
    }
    else {
      return null;
    }
  }

  @Override
  public void informChildReqSat(Requirement childReq, Sequence seq) {
  }

  @Override
  public void informChildReqNotSat(Requirement childReq) {
  }

  @Override
  public List<String> createEnsureGenOrder(List<String> paramNames) {
    return null;
  }
  
  @Override
  public DeductResult getDeductResult(Summary summary) {
    return null;
  }
  
  @Override
  public int getSummaryCount() {
    return m_summaries.size();
  }

  private final List<Summary> m_summaries;
}
