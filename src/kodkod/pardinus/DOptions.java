package kodkod.pardinus;

import kodkod.engine.config.Options;

public class DOptions extends Options {
	// the number of parallel processes
	private int threads = 4;

	private Modes mode = Modes.PARALLEL;

	public enum Modes {
		BATCH, 
		SEQUENTIAL,
		PARALLEL,
		HYBRID,
		INCREMENTAL,
		STATS;
	}

	public DOptions () {
		super();
	}

	public DOptions (Options options) {
		super(options);
	}
	
	/**
	 * Sets the number of threads that will be launched in parallel.
	 * @param threads
	 */
	public void setThreads(int threads) {
		this.threads = threads;
	}

	public int threads() {
		return threads;
	}

	public Modes getMode() {
		return mode;
	}

	public void setMode(Modes mode) {
		this.mode = mode;
	}
	
	
}
