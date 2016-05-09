package kodkod.pardinus.target;

/**
 * A SAT solver with support for partial satisfaction with weights.
 * pt.uminho.haslab
 */

public interface WTargetOrientedSATSolver extends TargetOrientedSATSolver {
	/**
	 * Adds a weighted target.
	 * pt.uminho.haslab
	 * @param lit the target
	 * @param weight the weight
	 */
	public boolean addWeight(int lit, int weight);
}
