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

import kodkod.engine.PrimitiveFactory;

/**
 * The options required by a target-oriented model finding problem.
 * 
 * @author Nuno Macedo // [HASLab] model finding hierarchy
 *
 * @param <S>
 *            the {@link kodkod.engine.PrimitiveSolver primitive solver}
 *            factory.
 */
public interface TargetOptions<S extends PrimitiveFactory<?>> extends
		PardinusOptions<S> {

	/**
	 * Whether the solver to run in target-oriented mode. This is different than
	 * simply setting the target-oriented mode to default, since in that case
	 * the target-oriented constructs are still initialized, but ignored for
	 * that particular execution.
	 * 
	 * @return Whether to initialize target-oriented constructs.
	 */
	public boolean runTarget();

	/**
	 * Instructs the solver to run in target-oriented mode.
	 * 
	 * @param runTarget
	 *            Whether to initialize target-oriented constructs.
	 */
	public void setRunTarget(boolean runTarget);

	/**
	 * The target-oriented mode that will be followed by the solver.
	 * 
	 * @return the target-oriented mode followed by the solver.
	 */
	public TMode targetMode();

	/**
	 * Instructs the solver to solve the problem in a specific target-oriented
	 * mode. This assumes that the target-oriented constructs were initialized
	 * (i.e., runTarget() = true), even if running in default mode.
	 * 
	 * @param the
	 *            target-oriented mode followed by the solver.
	 */
	public void setTargetMode(TMode mode);

	public enum TMode {
		DEFAULT, FAR, CLOSE
	}

}
