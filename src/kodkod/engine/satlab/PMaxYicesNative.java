package kodkod.engine.satlab;

import kodkod.engine.satlab.pardinus.WTargetSATSolver;


/**
 * 
 * @author tmg
 *
 */

public class PMaxYicesNative extends Yices implements WTargetSATSolver {


	private int targetCount;
	
	public PMaxYicesNative(){
		super();
		targetCount = 0;
	}
	
	static {
		loadLibrary(PMaxYicesNative.class);
	}

	@Override
	native boolean solve(long peer);

	@Override
	public int numberOfTargets() {
		return targetCount;
	}

	@Override
	public boolean addTarget(int lit) {
		// TODO Auto-generated method stub
		targetCount++;
		return addTarget(super.peer(),lit,array);
	}
	
	native boolean addTarget(long peer ,int lit,long array);

	@Override
	public boolean clearTargets() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean addWeight(int lit, int weight) {
		// TODO Auto-generated method stub
		return false;
	} 
}
	
