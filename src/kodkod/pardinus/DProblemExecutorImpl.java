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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.AtomicInteger;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A concretization of a decomposed problem executor designed to retrieve a
 * single SAT solution. Terminates once a SAT integrated / amalgatamted problem
 * is found or when every configuration has been explored.
 * 
 * @see kodkod.pardinus.DProblemExecutor
 * @author nmm, ejp
 */
public class DProblemExecutorImpl extends DProblemExecutor {

	/** the queue of solvers to be launched */
	private final List<DSolution> problem_queue = new ArrayList<DSolution>();

	/** the number of effectively running solvers */
	private final AtomicInteger running = new AtomicInteger(0);

	/** the queue of found SAT solutions (or poison) */
	private final BlockingQueue<DSolution> solution_queue = new LinkedBlockingQueue<DSolution>(10);

	/** whether the amalgamated problem will be launched */
	private final boolean hybrid;

	/** whether the amalgamated solver is currently running */
	private boolean amalgamated_running = false;

	/**
	 * Constructs an implementation of a decomposed problem solver with support for hybrid model.
	 *
	 * @see kodkod.pardinus.DProblemExecutor#DProblemExecutor(Formula, Formula, Bounds, Bounds, Solver, int)
	 */
	public DProblemExecutorImpl(Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver, int n, boolean it) {
		super(f1, f2, b1, b2, solver, n);
		this.hybrid = it;
	}

	/**
	 * Registers the solution and shutdowns the executor if the caller is the
	 * amalgamated problem, SAT integrated problem or last integrated problem.
	 * 
	 * @see kodkod.pardinus.DProblemExecutor#end(kkpartition.PProblem)
	 */
	@Override
	public void end(DSolution sol) {
		try {
			running.decrementAndGet();
			if (sol.sat())
				solution_queue.put(sol);
			// if the batch terminates, then shutdown the executor
			if (!(sol instanceof IProblem)) {
				amalgamated_running = false;
				shutdown();
			} else {
				// if every process has been launched and there is none running,
				// shutdown the executor
				if (executor.isShutdown()) {
					if (running.get() == 0 || (running.get() == 1 && amalgamated_running))
						shutdown();
				}
				// if a SAT integrated problem terminated, shutdown the executor
				else if (sol.sat())
					shutdown();

			}
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Shuts down the executor by inserting the poison token into the solution
	 * queue and sending a termination signal to every running thread.
	 * 
	 * @throws InterruptedException
	 *             if the solution queue is interrupted
	 */
	private void shutdown() throws InterruptedException {
		if (!Thread.currentThread().isInterrupted())
			solution_queue.put(DSolution.DONE);
		running.set(0);
		if (!executor.isTerminated())
			executor.shutdownNow();
	}

	/**
	 * Launches the parallel finders to solve the decomposed problem until the
	 * partial problem is unsatisfiable. The processes are handled by an
	 * executor that launched as many threads as defined by the options.
	 * Launches an amalgamated problem if in hybrid mode.
	 *
	 * @see kodkod.pardinus.DProblemExecutorr#run()
	 */
	@Override
	public void run() {
		// if hybrid mode, launch the amalgamated problem
		if (hybrid) {
			DSolution amalg = new DSolution(this, formula1.and(formula2), merge(bounds1, bounds2));
			amalg.setPriority(MAX_PRIORITY);
			executor.execute(amalg);
			running.incrementAndGet();
			amalgamated_running = true;
		}

		Iterator<Solution> configs = solver.solveAll(formula1, bounds1);
		boolean first = true;

		while (configs.hasNext() && !executor.isShutdown()) {
			// collects a batch of configurations
			while (configs.hasNext() && problem_queue.size() < 200) {
				Solution config = configs.next();

				if (config.unsat()) {
					// when there is no configuration no solver will ever
					// callback
					// so it must be terminated here
					if (first)
						try {
							shutdown();
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
				} else {
					DSolution problem = new IProblem(config, this);
					problem.setPriority(MIN_PRIORITY);
					problem_queue.add(problem);
				}

				first = false;

			}
			// launches a batch of integrated problems
			while (!problem_queue.isEmpty() && !executor.isShutdown()) {
				DSolution problem = problem_queue.remove(0/*
														 * problem_queue.size()
														 * - 1
														 */);
				executor.execute(problem);
				running.incrementAndGet();
			}
		}
		executor.shutdown();
	}

	/**
	 * Waits until a single solutions is added to the solution queue.
	 * 
	 * @see kodkod.pardinus.DProblemExecutor#waitUntil()
	 */
	@Override
	public DSolution waitUntil() throws InterruptedException {
		DSolution sol = null;
		sol = solution_queue.take();
		return sol;
	}

	/**
	 * Merges two problem bounds into a single one.
	 * 
	 * @param b1
	 *            the base bounds.
	 * @param b2
	 *            the bounds to be merged.
	 * @return the merged bounds.
	 */
	private static Bounds merge(Bounds b1, Bounds b2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return b3;
	}

}
