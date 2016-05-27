package kodkod.engine.config;

import kodkod.engine.PrimitiveFactory;

public interface TargetOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	public TMode getTargetMode();
	
	public void setTargetMode(TMode mode);
	
	public enum TMode {
		DEFAULT,
		FAR,
		CLOSE
	}

}
