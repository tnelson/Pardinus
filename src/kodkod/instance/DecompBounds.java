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
package kodkod.instance;

import java.util.LinkedHashMap;

import kodkod.ast.Relation;
import kodkod.util.ints.SparseSequence;

/**
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
public class DecompBounds extends Bounds {

	public Bounds bounds2;
	
	public DecompBounds(Bounds bounds1, Bounds bounds2) {
		super(bounds1.universe().factory(),bounds1.lowerBounds(),bounds1.upperBounds(),bounds1.targets(),bounds1.weights(),bounds1.intBounds());
		this.bounds2 = bounds2;
	}
	
	public DecompBounds(TupleFactory factory, LinkedHashMap<Relation, TupleSet> lowers,
			LinkedHashMap<Relation, TupleSet> uppers, LinkedHashMap<Relation, TupleSet> targets,
			LinkedHashMap<Relation, Integer> weights, SparseSequence<TupleSet> ints, Bounds bounds2) {
		super(factory,lowers,uppers,targets,weights,ints);
		this.bounds2 = bounds2;
	}

	public DecompBounds clone() {
		try {
			return new DecompBounds(universe().factory(), new LinkedHashMap<Relation, TupleSet>(lowerBounds()),
					new LinkedHashMap<Relation, TupleSet>(upperBounds()), new LinkedHashMap<Relation, TupleSet>(targets()),
					new LinkedHashMap<Relation, Integer>(weights()), intBounds().clone(), bounds2.clone());
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

}
