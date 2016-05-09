/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2015-present, Nuno Macedo
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
package kodkod.pardinus.decomp;

import kodkod.engine.config.Options;

public class DOptions extends Options {
	// the number of parallel processes
	private int threads = 4;

	private Modes mode = Modes.PARALLEL;

	public enum Modes {
		BATCH, 
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
