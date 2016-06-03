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
package kodkod.instance;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import kodkod.ast.Relation;
import kodkod.util.ints.Ints;
import kodkod.util.ints.SparseSequence;

/**
 * Represents a temporal model (an instance) of a temporal relational formula,
 * which is a mapping from time instants to a mapping from
 * {@link kodkod.ast.Relation relations} and integers to
 * {@link kodkod.instance.TupleSet sets of tuples} drawn from a given
 * {@link kodkod.instance.Universe universe}. The methods inherited from regular
 * {@link kodkod.instance.Instance instances} act upon the initial state.
 * 
 * @author nmm
 *
 */
public class TemporalInstance extends Instance {
	private final Map<Integer, Map<Relation, TupleSet>> tuples;
	private int loop = -1;
	private int max = -1;
	
	private TemporalInstance(Universe u, Map<Integer, Map<Relation, TupleSet>> tuples, SparseSequence<TupleSet> ints, int loop) {
		super(u, tuples.get(0), ints);
		this.tuples = tuples;
		this.loop = loop;
	}

	public TemporalInstance(Universe universe) {
		super(universe);
		if (universe == null)
			throw new NullPointerException("universe=null");
		this.tuples = new LinkedHashMap<Integer, Map<Relation, TupleSet>>();
		this.loop = -1;
	}

	public Map<Relation, TupleSet> relationTuples(int step) {
		return Collections.unmodifiableMap(tuples.get(step));
	}

	public void add(Relation relation, TupleSet s, int step) {
		if (!s.universe().equals(this.universe()))
			throw new IllegalArgumentException("s.universe!=this.universe");
		if (relation.arity() != s.arity())
			throw new IllegalArgumentException("relation.arity!=s.arity");
		max = max<step?step:max;
		Map<Relation, TupleSet> ts = tuples.get(step);
		if (ts == null)
			ts = new LinkedHashMap<Relation, TupleSet>();
		ts.put(relation, s);
		tuples.put(step, ts);
		if (step == 0)
			super.add(relation, s);
	}

	@Override
	public void add(Relation relation, TupleSet s) {
		add(relation, s, 0);
	}

	public TupleSet tuples(Relation relation, int step) {
		return tuples.get(step).get(relation);
	}
	
	public int loop() {
		return loop;
	}

	public void setLoop(int loop) {
		this.loop = loop;
	}
	
	public Iterator<Integer> stepIterator() {
		if (loop>max)
			throw new UnsupportedOperationException("loop larger than length");
		return new Iterator<Integer>() {
			int curr = -1;

			@Override
			public boolean hasNext() {
				return loop >= 0 || curr < max;
			}

			@Override
			public Integer next() {
				if (!hasNext())
					throw new UnsupportedOperationException("no next");
				curr = curr<max?curr+1:loop;
				return curr;
			}
			
		};
		
	}

	/**
	 * Returns an unmodifiable view of this instance.
	 * 
	 * @return an unmodifiable view of this instance.
	 */
	@Override
	public Instance unmodifiableView() {
		return new TemporalInstance(this.universe(), Collections.unmodifiableMap(tuples),
				Ints.unmodifiableSequence(this.intTuples()), loop);
	}

	/**
	 * Returns a deep copy of this Instance object.
	 * 
	 * @return a deep copy of this Instance object.
	 */
	@Override
	public Instance clone() {
		try {
			return new TemporalInstance(this.universe(), new LinkedHashMap<Integer, Map<Relation, TupleSet>>(tuples),
					this.intTuples().clone(), loop);
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Integer i : tuples.keySet())
			sb.append("\nrelations " + i + ": " + tuples.get(i).toString());
		sb.append("\nints: " + this.intTuples());
		return sb.toString();
	}

}
