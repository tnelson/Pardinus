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
package kodkod.pardinus.decomp;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A decomposed model finding problem.
 * @author nmm
 *
 */
public class DSolution extends Thread {

	public static DSolution DONE = new DSolution(null, null, null);
	final private Solver solver;
	
	private Solution solution;
	final public Bounds bounds;
	final public Formula formula;
	final public DProblemExecutor executor;

	public DSolution(DProblemExecutor manager, Formula formula, Bounds bnds) {
		this.executor = manager;
		if (this.executor != null) {
			solver = new Solver(this.executor.solver.options());
			this.bounds = bnds;
			this.formula = formula;
		} else {
			this.solver = null;
			this.formula = null;
			this.bounds = null;
		}
	}

	public void run() {
//		System.out.println("started: "+Thread.currentThread().getId());
		solution = solver.solve(formula,bounds);
		solver.free();
//		System.out.println("ended1: "+Thread.currentThread().getId()+", "+Thread.currentThread().isInterrupted());
		if (!Thread.currentThread().isInterrupted()) executor.end(this);
//		System.out.println("ended2: "+Thread.currentThread().getId());
	}

	public boolean sat() {
		if (solution == null) return false;
		return solution.sat();
	}

	public Solution getSolution() {
		return solution;
	}

	public long getSolveTime() {
		if (solution == null) return -1;
		return solution.stats().solvingTime()+solution.stats().translationTime();
	}

	public String toString() {
		if (solution==null) return "B: UNSOLVED";
		return "B: "+solution.outcome() + "\t" + getSolveTime();
	}
	
}