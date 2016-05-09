package kodkod.pardinus.target;

import kodkod.engine.satlab.SATSolver;

/**
 * A SAT solver with support for partial satisfaction.
 * pt.uminho.haslab
 */

public interface TargetOrientedSATSolver extends SATSolver {
		
	/**
	 * The current number of target literals.
	 * pt.uminho.haslab
	 */
	public abstract int numberOfTargets();

	/**
	 * Adds a target.
	 * pt.uminho.haslab
	 * @param lit the target
	 */
	public abstract boolean addTarget(int lit);

	/**
	 * Clears the targets. Needed for solution enumeration.
	 * pt.uminho.haslab
	 * @param lit the target
	 * @param weight the weight
	 */	
	public abstract boolean clearTargets();

}
