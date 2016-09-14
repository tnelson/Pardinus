/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
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
 * The options required by the {@link kodkod.engine.TemporalSolver temporal
 * solvers} to deploy temporal problems.
 * 
 * @author nmm (pt.uminho.haslab)
 *
 * @param <S>
 *            the {@link kodkod.engine.PrimitiveSolver primitive solver}
 *            factory.
 */
public interface TemporalOptions<S extends PrimitiveFactory<?>> extends PardinusOptions<S> {

	/**
	 * The maximum trace length that will be explored by the temporal model
	 * finder.
	 * 
	 * @return the maximum trace length.
	 */
	public int maxTraceLength();

	/**
	 * Updates the maximum trace length that will be explored by the temporal
	 * model finder.
	 * 
	 * @param traceLength
	 *            the new maximum trace length.
	 */
	public void setMaxTraceLength(int traceLength);

}
