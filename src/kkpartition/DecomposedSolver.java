package kkpartition;

import kkpartition.DecomposedOptions.Modes;
import kodkod.ast.Formula;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

public class DecomposedSolver {

	// the solver used in the parallelization
	final private Solver solver;

	// this solver's problem manager
	private ProblemManager manager;

	private DecomposedOptions options;

	public DecomposedSolver(Solver solver) {
		options = new DecomposedOptions();
		this.solver = solver;
		if (!solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
	}

	public DecomposedSolver(Solver solver, DecomposedOptions opt) {
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
	 * @throws InterruptedException 
	 */
	public PProblem solve(Bounds b1, Bounds b2, Formula f1, Formula f2) throws InterruptedException {
		if (options.getMode() == Modes.STATS)
			manager = new ConfigStatsManager(f1,f2,b1,b2,solver,options.threads());
		else if (options.getMode() == Modes.HYBRID)
			manager = new PProblemManager(f1,f2,b1,b2,solver,options.threads(),true);
		else
			manager = new PProblemManager(f1,f2,b1,b2,solver,options.threads(),false);
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
	public ProblemManager manager() {
		return manager;
	}

	public DecomposedOptions options() {
		return options;
	}

	public void free() {
		// TODO Auto-generated method stub		
	}



}
