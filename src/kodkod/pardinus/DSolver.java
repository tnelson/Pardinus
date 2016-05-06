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
 * @author nmm, ejp
 *
 */
public class DSolver {

	/** the regular Kodkod solver used in the parallelization */
	final public Solver solver;

	/** a manager for the decomposed solving process */
	private DProblemExecutor executor;

	/** the decomposed problem options */
	final public DOptions options;

	/**
	 * Constructs a new decomposed solver built over a standard Kodkod
	 * {@link kodkod.engine.Solver solver}. The solving
	 * {@link kodkod.engine.config.Options options} are retrieved from the
	 * regular solver.
	 * 
	 * @param solver
	 *            the regular solver over which the decomposed solver is built.
	 * @throws IllegalArgumentException
	 *             if the solver is not incremental.
	 */
	public DSolver(Solver solver) {
		if (solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
		this.options = new DOptions(solver.options());
		this.solver = solver;
	}

	/**
	 * Constructs a new decomposed solver built over a standard Kodkod
	 * {@link kodkod.engine.Solver solver} given defined decomposed solving
	 * options.
	 * 
	 * @param solver
	 *            the regular solver over which the decomposed solver is built.
	 * @param opt
	 *            the options for the decomposed solver.
	 * @throws IllegalArgumentException
	 *             if the solver is not incremental.
	 */
	public DSolver(Solver solver, DOptions opt) {
		if (solver.options().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
		this.options = opt;
		this.solver = solver;
	}

	/**
	 * Solves a decomposed model finding problem, comprised by a pair of
	 * {@link kodkod.ast.Formula formulas} and a pair of
	 * {@link kodkod.instance.Bounds bounds}. Essentially launches an
	 * {@link kodkod.pardinus.DProblemExecutor executor} to handle the
	 * decomposed problem in parallel, given the defined
	 * {@link kodkod.pardinus.DOptions options}.
	 * 
	 * @param b1
	 *            the partial problem bounds.
	 * @param b2
	 *            the remainder problem bounds.
	 * @param f1
	 *            the partial problem formula.
	 * @param f2
	 *            the remainder problem formula.
	 * @requires f1 to be defined over b1 and f2 over b2.
	 * @return a decomposed solution.
	 * @throws InterruptedException
	 *             if the solving process is interrupted.
	 */
	public DSolution solve(Bounds b1, Bounds b2, Formula f1, Formula f2) throws InterruptedException {
		if (options.getMode() == Modes.STATS)
			executor = new StatsExecutor(f1, f2, b1, b2, solver, options.threads());
		else if (options.getMode() == Modes.HYBRID)
			executor = new DProblemExecutorImpl(f1, f2, b1, b2, solver, options.threads(), true);
		else
			executor = new DProblemExecutorImpl(f1, f2, b1, b2, solver, options.threads(), false);
		executor.start();
		DSolution sol = executor.waitUntil();
		executor.terminate();
		return sol;
	}

	/**
	 * Retrieves the decomposed problem executor that handled the decomposed problem.
	 * 
	 * @return the decomposed problem executor that solved the problem.
	 */
	public DProblemExecutor executor() {
		return executor;
	}

	/**
	 * Releases the resources, if any.
	 */
	public void free() {}

}
