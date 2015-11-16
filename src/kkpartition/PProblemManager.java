package kkpartition;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.AtomicInteger;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * Created by macbookpro on 19/10/15.
 */
public class PProblemManager extends Thread {

	public final Bounds bound1, bound2;
	public final Solver solver;
	public final Formula formula;
	private Iterator<Solution> configs;

	private final List<PProblem> problem_queue = new ArrayList<PProblem>();
	private final BlockingQueue<PProblem> solution_queue = new LinkedBlockingQueue<PProblem>(10);
	// replace by new ThreadPoolExecutor(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue) to manage LIFO
	ExecutorService executor;

	private final AtomicInteger running = new AtomicInteger(0);

	public PProblemManager(Iterator<Solution> sol, Formula form, Bounds b1, Bounds b2, Solver solver, int n) {
		this.configs = sol;
		this.formula = form;
		this.bound1 = b1;
		this.bound2 = b2;
		this.solver = solver;
		this.executor = Executors.newFixedThreadPool(n);
	}

	/**
	 * Called by a problem when finished solving.
	 * @param sol
	 */
	public void end(PProblem sol) {
		try {
			solution_queue.put(sol);
			// tests if there are no more running processes and if the executor is shutdown
			// if so throws poison
			if (running.decrementAndGet() == 0 /*&& executor.isShutdown()*/) solution_queue.put(PProblem.DONE);
		} catch (InterruptedException e) { 
			// will be interrupted by the executor when the manager is terminated
		}
	}

	public void run() {
		boolean first = true;
		while (configs.hasNext() && !executor.isShutdown()) {
			while (configs.hasNext() && problem_queue.size() <= 100) {
				Solution config = configs.next();
				if (config.sat()) {
					PProblem problem = new PProblem (config, this);
					problem_queue.add(problem);
				} else {
					// poison is thrown when a process ends and there are no others
					// but if all configs are UNSAT, no process will ever end
					if (first)
						try {
							solution_queue.put(PProblem.DONE);
						} catch (InterruptedException e) { e.printStackTrace(); }
				}
				first = false;
			}
			while (!problem_queue.isEmpty() && !executor.isShutdown()) { 
				PProblem problem = problem_queue.remove(0/*problem_queue.size() - 1*/);
				executor.execute(problem);
				running.incrementAndGet();
			}
		}
		executor.shutdown();
	}

	/**
	 * Waits until there is a solution available.
	 * @return
	 */
	public PProblem waitUntil() {
		PProblem sol = null;
		try {
			sol = solution_queue.take();
		} catch (InterruptedException e) { 
			e.printStackTrace(); 
		}
		return sol;
	}

	public void terminate () {
		executor.shutdownNow();
	}


}
