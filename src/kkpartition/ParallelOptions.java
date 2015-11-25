package kkpartition;

import kodkod.engine.config.Options;

public class ParallelOptions {
	// the number of parallel processes
	private int threads = 4;
	// whether it will run in hybrid mode
	private boolean hybrid = true;


	public ParallelOptions () {
	
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
	
	/**
	 * Sets whether to run in hybrid model.
	 * @param threads
	 */
	public void setHybrid(boolean hybrid) {
		this.hybrid = hybrid;
	}

	public boolean isHybrid() {
		return hybrid;
	}
	
	
}
