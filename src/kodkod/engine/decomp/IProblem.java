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
package kodkod.engine.decomp;


import java.util.Iterator;

import kodkod.engine.Solution;

/**
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
public class IProblem extends DProblem {

	final public Solution config;

	public IProblem(Solution cfg, DProblemExecutor manager) {
		super(manager, manager.formula, manager.bounds.integrated(cfg));
		this.config = cfg;
	}
	
	public IProblem(Solution cfg, DProblemExecutor manager, Iterator<Solution> sols) {
		super(manager, manager.formula, manager.bounds.integrated(cfg), sols);
		this.config = cfg;
	}

	public IProblem next() {
		return new IProblem(config, executor, getIterator());
	}
	
}