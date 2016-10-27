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
import java.util.Map;

import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.util.ints.SparseSequence;

/**
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
public class DecompBounds extends Bounds {

	public final boolean integrated;

	public final RelativeBounds amalgamated;

	public boolean trivial_config;

	public DecompBounds(Bounds bounds1, Bounds bounds2) {
		super(bounds1.universe().factory(), bounds1.lowerBounds(), bounds1
				.upperBounds(), bounds1.intBounds());
		this.amalgamated = new RelativeBounds(bounds1);
		for (Relation r : bounds2.relations())
			this.amalgamated.bound(r, bounds2.lowerBound(r), bounds2.upperBound(r));
		if (bounds2 instanceof RelativeBounds)
			for (Relation r : ((RelativeBounds) bounds2).relrelations())
				this.amalgamated.bound(r, ((RelativeBounds) bounds2).lowerRelBounds(r), ((RelativeBounds) bounds2).upperRelBounds(r));

		
		integrated = false;
		trivial_config = false;
	}

	DecompBounds(TupleFactory factory, Map<Relation, TupleSet> lowers,
			Map<Relation, TupleSet> uppers, SparseSequence<TupleSet> ints,
			Bounds bounds2, boolean integrated, boolean trivial_config) {
		super(factory, lowers, uppers, ints);
		this.amalgamated = new RelativeBounds (bounds2);
		this.trivial_config = trivial_config;
		this.integrated = integrated;
	}

	public DecompBounds clone() {
		try {
			return new DecompBounds(universe().factory(),
					new LinkedHashMap<Relation, TupleSet>(lowerBounds()),
					new LinkedHashMap<Relation, TupleSet>(upperBounds()),
					intBounds().clone(), new RelativeBounds(amalgamated), integrated, trivial_config);
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	public Bounds amalgamated() {
		return amalgamated;
	}

	public DecompBounds integrated(Solution sol) {
		if (integrated)
			throw new IllegalAccessError("Can't");
		
		RelativeBounds integrated = new RelativeBounds(amalgamated);
		
		if (sol.stats().primaryVariables() == 0) trivial_config = true;
		
		for (Relation e : this.relations()) {
			if (getTupleConfiguration(e.name(), sol.instance()) != null) {
				integrated.boundExactly(e,
						getTupleConfiguration(e.name(), sol.instance()));
			}
		}
		
		for (Integer i : sol.instance().ints().toArray())
			integrated.boundExactly(i, integrated.universe().factory().setOf(i));

		integrated.resolve();
		
		DecompBounds res = null;
		try {
			res = new DecompBounds(universe().factory(),
					integrated.lowerBounds(), integrated.upperBounds(),
					integrated.intBounds().clone(), this.amalgamated.clone(), true, trivial_config);
		} catch (CloneNotSupportedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		return res;
	}

	private static TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet()) {
			if (r.name().equals(name)) {
				return s.relationTuples().get(r);
			}
		}
		return null;
	}

}
