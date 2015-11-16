package kkpartition;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

public class PProblem extends Thread {

	public static PProblem DONE = new PProblem(null, null);

	private Solution solution;
	final public Solution config;
	final public Bounds problem_bounds;
	final public Formula formula;
	final public PProblemManager manager;

	public PProblem(Solution cfg, PProblemManager manager) {
		this.config = cfg;
		this.manager = manager;
		if (this.manager != null) {
			this.formula = this.manager.formula;
			this.problem_bounds = configBounds(this.manager.bound1, this.manager.bound2, cfg);
		} else {
			this.formula = null;
			this.problem_bounds = null;
		}
	}

	public void run() {
		Solver solver = new Solver(manager.solver.options());
		solution = solver.solve(formula,problem_bounds);
		manager.end(this);
	}
	
	/**
	 * Sets a configuration solution as exact bounds for the problem.
	 * @param b1
	 * @param b2
	 * @param s
	 * @return
	 */
	private Bounds configBounds(Bounds b1, Bounds b2, Solution s) {
		Bounds b3 = b2.clone();

		for (Relation e : b1.upperBounds().keySet()) {
			if (getTupleConfiguration(e.name(), s.instance()) != null) {
				b3.boundExactly(e, getTupleConfiguration(e.name(), s.instance()));
			}
		}

		for (Integer i : s.instance().ints().toArray())
			b3.boundExactly(i, b3.universe().factory().setOf(i));

		return b3;
	}

	private TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet()) {
			if (r.name().equals(name)) {
				return s.relationTuples().get(r);
			}
		}
		return null;
	}

	public boolean sat() {
		return solution.sat();
	}

	public Solution getSolution() {
		return solution;
	}

	public long getSolveTime() {
		if (solution == null) return -1;
		return solution.stats().solvingTime()+solution.stats().translationTime();
	}

	public long getConfigTime() {
		if (config == null) return -1;
		return config.stats().solvingTime()+config.stats().translationTime();
	}
	
	/**
	 * Calculates the size of the configuration (number of tuples in the relations).
	 * @return
	 */
	private int configSize() {
		int c = 0;
		for (TupleSet x : config.instance().relationTuples().values())
			c = c + x.size();
		return c;
	}
	
	public String toString() {
		if (config==null) return "POISON";
		if (solution==null) return "UNSOLVED";
		return configSize() + "\t" + getConfigTime() + "\t" + solution.outcome() + "\t" + getSolveTime();
	}
	
	public void interrupt() {
		
	}

}