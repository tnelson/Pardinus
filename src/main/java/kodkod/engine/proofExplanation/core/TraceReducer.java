package kodkod.engine.proofExplanation.core;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.LazyTrace;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

import java.util.HashSet;
import java.util.Set;

/**
 * A class meant to encapsulate trace and core reducing behavior.
 * Operates on ResolutionTraces obtained from UNSAT proofs, providing
 * functionality to reduce them according to a set of assumption literals.
 */
public class TraceReducer {

  // TODO: how do you get the ints in `assumps` to agree with those in trace?
  // > option: getting the trace, seeing the ints corresponding to literals, and then propagating?
  //   - but in this case, meaning is lost in translation and would be hard for user to discern

  public ResolutionTrace reduce(ResolutionTrace trace, IntSet assumps) {
    // need functionality to:
    // - unit propagate
    // - topological sort
    // - set! clauses

    // TODO: topological sort on edges
    IntSet axiomIndices = trace.axioms();
    Set<Clause> axiomClauses = new HashSet<>();
    IntIterator axiomIndicesIt = axiomIndices.iterator();
    while (axiomIndicesIt.hasNext()) {
      // note that as is, clauses returned by `.get` are guaranteed to be immutable.
      // swetabhch: changed literals, hashCode in Clause to public
      Clause axiom = trace.get(axiomIndicesIt.next());
      axiomClauses.add(axiom);
    }



    int[][] retTrace = {};
    return new LazyTrace(retTrace, 0);
  }

  /**
   * Propagates a set of literals on a clause, thus modifying the clause's set
   * of literals in-place.
   * @param trace The resolution trace from which the given clause is drawn.
   * @param clause The clause on which propagation is to be done.
   * @param assumps A set of integers referring to the indices of the literals
   *                (from the trace) that are to be propagated.
   */
  public static void unitPropagateAll(ResolutionTrace trace, Clause clause, IntSet assumps) {

  }

  /**
   * Propagates a literal on a clause, thus modifying the clause's set of
   * literals in-place.
   * @param trace The resolution trace from which the given clause is drawn.
   * @param clause The clause on which propagation is to be done.
   * @param assump An integer referring to the index of the literal (from the
   *               trace) that is to be propagated.
   */
  public static void unitPropagate(ResolutionTrace trace, Clause clause, int assump) {
    
  }

}
