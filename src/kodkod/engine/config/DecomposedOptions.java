package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface DecomposedOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	public void setThreads(int threads);

	public int threads();

	public DMode getMode();

	public void setMode(DMode mode);
	
	public enum DMode {
		BATCH, 
		PARALLEL,
		HYBRID,
		INCREMENTAL,
		STATS;
	}
	
}
