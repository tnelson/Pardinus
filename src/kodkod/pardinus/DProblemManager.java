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
package kodkod.pardinus;

import java.util.List;

import kodkod.ast.Formula;
import kodkod.engine.Solver;
import kodkod.engine.Statistics;
import kodkod.instance.Bounds;


/**
 * 
 * @author nmm
 *
 */
abstract public class DProblemManager extends Thread {

	/**
	 * Called by a problem when finished solving.
	 * @param sol
	 */
	public abstract void end(DSolution sol);

	public abstract void run();

	/**
	 * Waits until there is a solution available.
	 * @return
	 * @throws InterruptedException 
	 */
	public abstract DSolution waitUntil() throws InterruptedException;

	public abstract void terminate() throws InterruptedException;

	public abstract List<DSolution> solutions();
	
	public abstract Bounds bounds1();

	public abstract Bounds bounds2();
	
	public abstract Formula formula1();

	public abstract Formula formula2();

	public abstract Solver solver();

	public abstract int getSats();

	public abstract long getConfigTimes();

	public abstract Statistics getConfigStats();

	public abstract int getVars();
	
	public abstract int getClauses();
	
}