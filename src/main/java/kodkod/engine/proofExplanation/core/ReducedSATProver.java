package kodkod.engine.proofExplanation.core;

import kodkod.engine.satlab.ReductionStrategy;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATProver;

public class ReducedSATProver implements SATProver {

    private ReducedResolutionTrace reducedTrace;
    private final UnsupportedOperationException UNSUPPORTED_EXCEPT = 
        new UnsupportedOperationException("ReducedSATProver does not support solving operations.");

    public ReducedSATProver(ReducedResolutionTrace reducedTrace) {
        this.reducedTrace = reducedTrace;
    }

    /** TODO: (change doc)
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATProver#proof()
	 */
    public ResolutionTrace proof() {
        return reducedTrace;
    }

    @Override
    public int numberOfVariables() {
        throw UNSUPPORTED_EXCEPT;
    }

    @Override
    public int numberOfClauses() {
        throw UNSUPPORTED_EXCEPT;
    }

    @Override
    public void addVariables(int numVars) {
        throw UNSUPPORTED_EXCEPT;
    }

    @Override
    public boolean addClause(int[] lits) {
        throw UNSUPPORTED_EXCEPT;
    }

    @Override
    public boolean solve() throws SATAbortedException {
        throw UNSUPPORTED_EXCEPT;
    }

    @Override
    public boolean valueOf(int variable) {
        throw UNSUPPORTED_EXCEPT;
    }

    /** TODO:
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATProver#free()
	 */
    public void free() {
        reducedTrace = null;
    }

    @Override
    public void reduce(ReductionStrategy strategy) {
        throw UNSUPPORTED_EXCEPT;
    }
    
}
