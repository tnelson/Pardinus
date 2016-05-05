/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2015-present, Nuno Macedo
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.pardinus;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;
import kodkod.pardinus.DOptions.Modes;

/**
 * A computational engine for solving relational satisfiability problems. Such a
 * problem is described by a pair {@link kodkod.ast.Formula formulas} in first
 * order relational logic; a pair of finite {@link kodkod.instance.Bounds
 * bounds} on the value of each {@link Relation relation} constrained by the
 * respective formulas; and a set of {@link kodkod.pardinus.DOptions options}
 * built over regular Kodkod {@link kodkod.engine.config.Options options}. The
 * decomposed solve relies on regular Kodkod {@link kodkod.engine.Solver
 * solvers} that are deployed in parallel. The solver returns a
 * {@link kodkod.pardinus.DSolution decomposed solution} that can be iterated.
 * 
 * @author nmm
 *
 */
public class DSolver {

	/** the regular Kodkod solver used in the parallelization */
	final private Solver solver;

	/** a manager for the decomposed solving process */
	private DProblemManager manager;

	/** the decomposed problem options */
	private DOptions options;

	public DSolver(Solver solver) {
		this.options = new DOptions();
		this.solver = solver;
		if (!solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
	}

	public DSolver(Solver solver, DOptions opt) {
		this.options = opt;
		this.solver = solver;
		if (!solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
	}

	/**
	 * Solves a partitioned problem in parallel.
	 * 
	 * @param b1
	 *            partition 1 bounds
	 * @param b2
	 *            partition 2 bounds
	 * @param f1
	 *            partition 1 formula
	 * @param f2
	 *            partition 2 formula
	 * @return a SAT solution or DONE
	 * @throws InterruptedException
	 */
	public DSolution solve(Bounds b1, Bounds b2, Formula f1, Formula f2) throws InterruptedException {
		if (options.getMode() == Modes.STATS)
			manager = new ConfigStatsManager(f1, f2, b1, b2, solver, options.threads());
		else if (options.getMode() == Modes.HYBRID)
			manager = new DProblemManagerImpl(f1, f2, b1, b2, solver, options.threads(), true);
		else
			manager = new DProblemManagerImpl(f1, f2, b1, b2, solver, options.threads(), false);
		manager.start();
		DSolution sol = manager.waitUntil();
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
	 * 
	 * @return
	 */
	public DProblemManager manager() {
		return manager;
	}

	public DOptions options() {
		return options;
	}

	public void free() {
		// TODO Auto-generated method stub
	}

}
