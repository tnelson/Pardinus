package kkpartition;

import kodkod.ast.Formula;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

public class ParallelSolver {

	// the solver used in the parallelization
	final private Solver solver;

	// the number of parallel processes
	private int threads = 4;
	// whether it will run in hybrid mode
	private boolean hybrid = true;

	// this solver's problem manager
	private PProblemManager manager;
	
	public ParallelSolver(Solver solver) {
		this.solver = solver;
		if (!solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
	}

	/**
	 * Solves a partitioned problem in parallel.
	 * @param b1 partition 1 bounds
	 * @param b2 partition 2 bounds
	 * @param f1 partition 1 formula
	 * @param f2 partition 2 formula
	 * @return a SAT solution or DONE
	 */
	public PProblem solve(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		manager = new PProblemManager(f1,f2,b1,b2,solver,threads,hybrid);
		manager.start();
		PProblem sol = manager.waitUntil();
		manager.terminate();
		return sol;
		}

	/**
	 * Sets the number of threads that will be launched in parallel.
	 * @param threads
	 */
	public void setThreads(int threads) {
		this.threads = threads;
	}

	/**
	 * Sets whether to run in hybrid model.
	 * @param threads
	 */
	public void setHybrid(boolean hybrid) {
		this.hybrid = hybrid;
	}

	/**
	 * Returns the problem manager for this solver.
	 * @return
	 */
	public PProblemManager manager() {
		return manager;
	}

}
