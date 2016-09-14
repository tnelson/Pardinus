package kodkod.engine.config;

import kodkod.engine.config.Options.IntEncoding;
import kodkod.engine.satlab.SATFactory;

public interface BoundedOptions extends PardinusOptions<SATFactory> {

	public int bitwidth();
	
	public void setBitwidth(int bitwidth);
	
	public boolean noOverflow();

	public void setNoOverflow(boolean noOverflow);

	public void setSymmetryBreaking(int symmetryBreaking);
	
	public void setSkolemDepth(int skolemDepth);
	
	public void setIntEncoding(IntEncoding encoding);
	
	public void setLogTranslation(int logTranslation);
	
	public void setCoreGranularity(int coreGranularity);
	
	public int symmetryBreaking();

	public int skolemDepth();

}
