package kodkod.engine.proofExplanation.core;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.LazyTrace;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

import java.util.*;

/**
 * A class meant to encapsulate trace and core reducing behavior.
 * Operates on ResolutionTraces obtained from UNSAT proofs, providing
 * functionality to reduce them according to a set of assumption literals.
 */
public class TraceReducer {

  // TODO: how do you get the ints in `assumps` to agree with those in trace?
  // > option: getting the trace, seeing the ints corresponding to literals, and then propagating?
  //   - but in this case, meaning is lost in translation and would be hard for user to discern

  /**
   * Takes in a {@linkplain ResolutionTrace} and an {@linkplain IntSet} representing
   * a set of assumptions and produces a "reduced" trace. A "reduced" trace is one where
   * the involved axioms are modified by unit propagating all assumptions on them, and
   * resolvents are re-established by resolving the modified clauses together.
   * The current draft of this function works to modify the {@linkplain ResolutionTrace} in-place.
   * @param trace The {@linkplain ResolutionTrace} to reduce.
   * @param assumps The {@linkplain IntSet} to propagate on the trace.
   */
  public void reduce(ResolutionTrace trace, IntSet assumps) {
    // need functionality to:
    // - unit propagate
    // - topological sort
    // - set! clauses
    // - resolve updated clauses

    // TODO: need a map from old clauses to new clauses if we're building a new trace
    //List<Clause> newTrace = new ArrayList<Clause>();

    // if we are operating on Clauses, then trace.iterator() gives us the Clauses
    // of the trace "in order", i.e. in a topologically sorted order
    Iterator<Clause> edgePlanIterator = trace.iterator();

    // note that on first pass of edgePlanIterator, we can also tell which Clauses
    // are axioms, and can integrate the unit propagation step in that pass
    while (edgePlanIterator.hasNext()) {
      Clause currClause = edgePlanIterator.next();
      boolean isAxiom = (currClause.numberOfAntecedents() == 0);
      if (isAxiom) {
        // performs unit propagation on the clause, removing literals from it in place
        // returns true if the clause contains the assumption literal, in which case the
        // clause is removed from the literal entirely
        boolean clauseBecomesTrue = unitPropagateAllAndReturnFlag(trace, currClause, assumps);
        if (clauseBecomesTrue) {
          edgePlanIterator.remove();
          // TODO: remove clause from the int[][] trace OR
        }
      } else {
        // TODO: new resolution + push step
        Iterator<Clause> antes = currClause.antecedents();
        // can use LazyTrace's `resolve` method, given the index of the resolvent
        // modify the current clause's set of literals

      }
    }

    // TODO: if we're working in-place, we also need a pruning step for the rest of the
    //  - trace, and an elaborate function to modify the trace matrix

    //int[][] retTrace = {};
    //return new LazyTrace(retTrace, 0);
  }

  /**
   * Propagates a literal on a copy of a clause, which gets a modified set of literals,
   * and returns an {@linkplain Optional} representing the result. The result has no
   * value present if the clause reduces to true.
   * @param clause The clause on which propagation is to be done.
   * @param assump An integer referring to the index of the literal (from the
   *               trace) that is to be propagated.
   * @return An optional containing the new clause, if the clause does not reduce to true.
   */
  /*
  public Optional<Clause> unitPropagate(Clause clause, int assump) {
    // look at the clause's set of literals
    // if an index is the same as the assump index, then the clause becomes true

    IntIterator literalIterator = clause.literals();
    while (literalIterator.hasNext()) {
      int nextLiteral = literalIterator.next();
      if (assump == -1 * nextLiteral) {
        literalIterator.remove();
      }
      if (assump == nextLiteral) {
        return true;
      }
    }
    return false;
  }

   */

  /**
   * Propagates a set of literals on a clause, thus modifying the clause's set
   * of literals in-place, and returns a flag indicating if the clause returns to true.
   * @param clause The clause on which propagation is to be done.
   * @param assumps A set of integers referring to the indices of the literals
   *                (from the trace) that are to be propagated.
   * @return A boolean indicating whether the clause reduces to true.
   */
  public boolean unitPropagateAllAndReturnFlag(ResolutionTrace origTrace, Clause clause, IntSet assumps) {
    IntIterator assumpsIterator = assumps.iterator();
    while (assumpsIterator.hasNext()) {
      if (unitPropagateAndReturnFlag(origTrace, clause, assumpsIterator.next())) {
        return true;
      }
    }
    return false;
  }

  /**
   * Propagates a literal on a clause, thus modifying the clause's set of
   * literals in-place, and returns a flag that indicates if the clause reduces to true.
   * @param clause The clause on which propagation is to be done.
   * @param assump An integer referring to the index of the literal (from the
   *               trace) that is to be propagated.
   * @return A boolean indicating whether the clause reduces to true.
   */
  public boolean unitPropagateAndReturnFlag(ResolutionTrace origTrace, Clause clause, int assump) {
    // look at the clause's set of literals
    // if an index is the same as the assump index, then the clause becomes true
    IntIterator literalIterator = clause.literals();
    while (literalIterator.hasNext()) {
      int nextLiteral = literalIterator.next();
      if (assump == -1 * nextLiteral) {
        literalIterator.remove();
        // TODO: obtain the trace matrix from `origTrace`, remove `assump` from origTrace[clauseNum]
      }
      if (assump == nextLiteral) {
        return true;
      }
    }
    return false;
  }

  //public boolean resolve(Iterator<Clause>)

}
