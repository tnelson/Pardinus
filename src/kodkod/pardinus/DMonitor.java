package kodkod.pardinus;

import kodkod.engine.Solution;

public interface DMonitor {

	public abstract void newConfig(Solution config);

	public abstract void newSolution(DSolution sol);

	public abstract long getSats();

	public abstract long getVars();

	public abstract long getClauses();

	public abstract void finishedLaunching();

	public abstract void done(boolean timeout);

	public abstract void terminated(boolean timeout);

}