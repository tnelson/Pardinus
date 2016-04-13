package kkpartition;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import com.apple.jobjc.Utils.Threads;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.instance.Bounds;

/**
 */
public class PProblemManager extends ProblemManager {

	private final Bounds bound1, bound2;
	private final Solver solver;
	private final Formula formula1;
	private final Formula formula2;

	private final List<PProblem> solutions = new ArrayList<PProblem>();
	private final List<PProblem> problem_queue = new ArrayList<PProblem>();
	private final BlockingQueue<PProblem> solution_queue = new LinkedBlockingQueue<PProblem>(10);
	// replace by new ThreadPoolExecutor(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue) to manage LIFO
	ExecutorService executor;

	private final AtomicInteger running = new AtomicInteger(0);
	private boolean hybrid;
	private boolean batch = false;

	public PProblemManager(Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver, int n, boolean it) {
		this.hybrid = it;
		this.formula1 = f1;
		this.formula2 = f2;
		this.bound1 = b1;
		this.bound2 = b2;
		this.solver = solver;
		this.executor = Executors.newFixedThreadPool(n);
	}

	/* (non-Javadoc)
	 * @see kkpartition.ProblemManager#end(kkpartition.PProblem)
	 */
	@Override
	public void end(PProblem sol) {
		try {
//			System.out.println(sol);
			running.decrementAndGet();
			solutions.add(sol); // should be atomic or solutions are lost
			if (sol.sat()) 
				solution_queue.put(sol);
			if (!(sol instanceof MProblem)) {
				batch = false;
				shutdown();
			}
			else {
				// tests if there are no more running processes and if the executor is shutdown
				// if so throws poison
				if (executor.isShutdown()) {
					if (running.get() == 0) 
						shutdown();
					else if (running.get() == 1 && batch) 
						shutdown();
				}
				else if (sol.sat()) shutdown(); 

			}
		} catch (InterruptedException e) { 
			e.printStackTrace();
		}
	}
	
	private void shutdown() throws InterruptedException {
		if (!Thread.currentThread().isInterrupted())
			solution_queue.put(PProblem.DONE);
		 running.set(0);
		 if (!executor.isTerminated()) 
			 executor.shutdownNow();
	}

	/* (non-Javadoc)
	 * @see kkpartition.ProblemManager#run()
	 */
	@Override
	public void run() {
		if(hybrid) {
			PProblem ppr = new PProblem(this, new ArrayList<Bounds>(Arrays.asList(merge(bound1, bound2))));
			ppr.setPriority(MAX_PRIORITY);
			executor.execute(ppr);
			running.incrementAndGet();
			batch = true;
		}
		
		Iterator<Solution> configs = solver.solveAll(formula1, bound1);
		boolean first = true;

		while (configs.hasNext() && !executor.isShutdown()) {
			while (configs.hasNext() && problem_queue.size() < 200) {
				List<Solution> current_configs = new ArrayList<Solution>();
				while (configs.hasNext() && current_configs.size() < 1) {
					Solution config = configs.next();
//					System.out.println(config.instance());
					if (config.sat()) {
						current_configs.add(config);
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
				if(!current_configs.isEmpty()) {
					PProblem problem = new MProblem (current_configs, this);
					problem.setPriority(MIN_PRIORITY);
					problem_queue.add(problem);
				}
			}
			while (!problem_queue.isEmpty() && !executor.isShutdown()) { 
				PProblem problem = problem_queue.remove(0/*problem_queue.size() - 1*/);
				executor.execute(problem);
				running.incrementAndGet();
			}
		}
		executor.shutdown();
	}

	/* (non-Javadoc)
	 * @see kkpartition.ProblemManager#waitUntil()
	 */
	@Override
	public PProblem waitUntil() throws InterruptedException {
		PProblem sol = null;
		sol = solution_queue.take();
		return sol;
	}

	/* (non-Javadoc)
	 * @see kkpartition.ProblemManager#terminate()
	 */
	@Override
	public void terminate () throws InterruptedException {
//		executor.awaitTermination(100000, TimeUnit.SECONDS);
	}

	private static Bounds merge(Bounds b1, Bounds b2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return b3;
	}
	
	/* (non-Javadoc)
	 * @see kkpartition.ProblemManager#solutions()
	 */
	@Override
	public List<PProblem> solutions() {
		return solutions;
	}

	@Override
	public Bounds bounds1() {
		return bound1;
	}

	@Override
	public Bounds bounds2() {
		return bound2;
	}

	@Override
	public Formula formula1() {
		return formula1;
	}

	@Override
	public Formula formula2() {
		return formula2;
	}

	@Override
	public Solver solver() {
		return solver;
	}

	@Override
	public int getSats() {
		return solution_queue.size();
	}

	@Override
	public long getConfigTimes() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Statistics getConfigStats() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getVars() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public int getClauses() {
		// TODO Auto-generated method stub
		return 0;
	}
}
