package kkpartition;

import kodkod.ast.Formula;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

public class ParallelSolver {

	public enum Modes {
		BATCH, 
		SEQUENTIAL,
		PARALLEL,
		HYBRID,
		INCREMENTAL;
	}
	
	public enum Solvers {
		GLUCOSE,
		MINISAT,
		SYRUP,
		PLINGELING;
	}
	
	// the solver used in the parallelization
	final private Solver solver;

	// this solver's problem manager
	private PProblemManager manager;

	private ParallelOptions options;
	
	public ParallelSolver(Solver solver) {
		options = new ParallelOptions();
		this.solver = solver;
		if (!solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
	}

	public ParallelSolver(Solver solver, ParallelOptions opt) {
		options = opt;
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
		manager = new PProblemManager(f1,f2,b1,b2,solver,options.threads(),options.isHybrid());
		manager.start();
		PProblem sol = manager.waitUntil();
		try {
			manager.terminate();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return sol;
		}

	/**
	 * Returns the problem manager for this solver.
	 * @return
	 */
	public PProblemManager manager() {
		return manager;
	}

	public ParallelOptions options() {
		return options;
	}

	public void free() {
		// TODO Auto-generated method stub		
	}

	
}
