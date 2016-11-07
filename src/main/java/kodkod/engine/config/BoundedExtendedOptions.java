/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.config;

import kodkod.engine.satlab.SATFactory;

/**
 * An implementation of options for bounded problems with every Pardinus
 * functionality (temporal, decomposed, target-oriented). Inherits from regular
 * Kodkod options (bounded).
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy, target-oriented, temporal and decomposed model finding
 */
public class BoundedExtendedOptions extends Options implements BoundedOptions,
		DecomposedOptions<SATFactory>, TemporalOptions<SATFactory>,
		TargetOptions<SATFactory> {

	public BoundedExtendedOptions() {
		super();
	}

	public BoundedExtendedOptions(BoundedExtendedOptions options) {
		super(options);
		this.setTargetMode(options.targetMode());
		this.setRunTarget(options.runTarget());
		this.setThreads(options.threads());
		this.setDecomposedMode(options.decomposedMode());
		this.setConfigOptions(options.configOptions());
		this.setMaxTraceLength(options.maxTraceLength());
	}

	// target-oriented solving

	private TMode target_mode = TMode.DEFAULT;
	private boolean runTarget = false;

	@Override
	public TMode targetMode() {
		return target_mode;
	}

	@Override
	public void setTargetMode(TMode mode) {
		target_mode = mode;
	}

	@Override
	public boolean runTarget() {
		return runTarget;
	}

	@Override
	public void setRunTarget(boolean runTarget) {
		this.runTarget = runTarget;
	}

	// decomposed solving
	private int threads = 4;

	private DMode mode = DMode.BATCH;
	private PardinusOptions<SATFactory> configOptions = this;

	/**
	 * Sets the number of threads that will be launched in parallel.
	 * 
	 * @param threads
	 */
	@Override
	public void setThreads(int threads) {
		this.threads = threads;
	}

	@Override
	public int threads() {
		return threads;
	}

	@Override
	public DMode decomposedMode() {
		return mode;
	}

	@Override
	public void setDecomposedMode(DMode mode) {
		this.mode = mode;
	}

	@Override
	public void setConfigOptions(PardinusOptions<SATFactory> opt) {
		configOptions = opt;
	}

	@Override
	public PardinusOptions<SATFactory> configOptions() {
		return configOptions;
	}

	// temporal solving

	private int trace_length = 20;

	@Override
	public void setMaxTraceLength(int trace_length) {
		this.trace_length = trace_length;
	}

	@Override
	public int maxTraceLength() {
		return trace_length;
	}

	
	public String toString() {
		StringBuilder b = new StringBuilder(super.toString());
		b.append("\n run target: ");
		b.append(runTarget);
		b.append("\n target mode: ");
		b.append(target_mode);
		b.append("\n threads: ");
		b.append(threads);
		b.append("\n decomposed mode: ");
		b.append(mode);
		b.append("\n max trace length: ");
		b.append(trace_length);
        return b.toString();
	}
}
