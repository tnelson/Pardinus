package kodkod.pardinus;

import java.util.List;

import kodkod.ast.Formula;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.instance.Bounds;

abstract public class ProblemManager extends Thread {

	/**
	 * Called by a problem when finished solving.
	 * @param sol
	 */
	public abstract void end(PProblem sol);

	public abstract void run();

	/**
	 * Waits until there is a solution available.
	 * @return
	 * @throws InterruptedException 
	 */
	public abstract PProblem waitUntil() throws InterruptedException;

	public abstract void terminate() throws InterruptedException;

	public abstract List<PProblem> solutions();
	
	public abstract Bounds bounds1();

	public abstract Bounds bounds2();
	
	public abstract Formula formula1();

	public abstract Formula formula2();

	public abstract Solver solver();

	public abstract int getSats();

	public abstract long getConfigTimes();

	public abstract Statistics getConfigStats();

	public abstract int getVars();
	
	public abstract int getClauses();
	
}