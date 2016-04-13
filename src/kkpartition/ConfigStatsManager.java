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
public class ConfigStatsManager extends ProblemManager {

	private final Bounds bound1, bound2;
	private final Solver solver;
	private final Formula formula1;
	private final Formula formula2;
	private long config_times = -1;
	private Statistics config_stats = null;
	private AtomicInteger sats = new AtomicInteger(0);
	private AtomicInteger vars = new AtomicInteger(0);
	private AtomicInteger clauses = new AtomicInteger(0);

	
	private final List<PProblem> solutions = new ArrayList<PProblem>();
	private final List<PProblem> problem_queue = new ArrayList<PProblem>();
	// replace by new ThreadPoolExecutor(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue) to manage LIFO
	ExecutorService executor;

	private final AtomicInteger running = new AtomicInteger(0);

	public ConfigStatsManager(Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver, int n) {
		this.formula1 = f1;
		this.formula2 = f2;
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
		if (sol.sat()) sats.incrementAndGet();
		vars.addAndGet(sol.getSolution().stats().primaryVariables());
		clauses.addAndGet(sol.getSolution().stats().clauses());
		running.decrementAndGet();
	    synchronized(this){
	    	solutions.add(sol);
	    }
	}
	

	public void run() {
		Iterator<Solution> configs = solver.solveAll(formula1, bound1);
		while (configs.hasNext() && !executor.isShutdown()) {
			while (configs.hasNext() && problem_queue.size() < 200) {
				List<Solution> current_configs = new ArrayList<Solution>();
				while (configs.hasNext() && current_configs.size() < 1) {
					Solution config = configs.next();
//					System.out.println(config.instance());
					if (config_times < 0) {
						config_times = config.stats().translationTime();
						config_stats = config.stats();
					}
					config_times += config.stats().solvingTime();
					if (config.sat()) 
						current_configs.add(config);
				}
				if(!current_configs.isEmpty()) {
					PProblem problem = new MProblem (current_configs, this);
					problem.setPriority(MIN_PRIORITY);
					problem_queue.add(problem);
				}
			}
			while (!problem_queue.isEmpty() && !executor.isShutdown()) { 
				PProblem problem = problem_queue.remove(/*0*/problem_queue.size() - 1);
//				executor.execute(problem);
				running.incrementAndGet();
			}
		}
		executor.shutdown();
	}

	/**
	 * Waits until there is a solution available.
	 * @return
	 * @throws InterruptedException 
	 */
	public PProblem waitUntil() throws InterruptedException {
		PProblem sol = null;
		executor.awaitTermination(10, TimeUnit.HOURS);
		return sol;
	}

	public void terminate () throws InterruptedException {
//		executor.awaitTermination(1000, TimeUnit.SECONDS);
	}
	
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
		return sats.intValue();
	}
	
	@Override
	public int getVars() {
		return vars.intValue();
	}
	
	@Override
	public int getClauses() {
		return clauses.intValue();
	}

	@Override
	public long getConfigTimes() {
		return config_times;
	}
	
	@Override
	public Statistics getConfigStats() {
		return config_stats;
	}
}
