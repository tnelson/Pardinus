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

import kodkod.ast.Formula;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;

/**
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
public abstract class DModel {

	/**
	 * Bounds of the first partition.
	 * 
	 * @return the partial problem bounds
	 */
	abstract public PardinusBounds bounds1();

	/**
	 * Bounds of the second partition.
	 * 
	 * @return the remainder problem bounds
	 */
	abstract public Bounds bounds2();

	public PardinusBounds bounds() { return new PardinusBounds(bounds1(), bounds2()); }
	
	/**
	 * Formula for the first partition. Formula must refer to every relation in
	 * bounds1().
	 * 
     * @return the first partition formula
	 */
	abstract public Formula partition1();

	/**
	 * Formula for the second partition.
	 * 
	 * @return the second partition formula
	 */
	abstract public Formula partition2();

	public Formula formula() { return partition1().and(partition2()); }

	/**
	 * The bits required to encode the model.
	 * 
	 * @return the required bitwidth
	 */
	abstract public int getBitwidth();

	abstract public String shortName();

}
