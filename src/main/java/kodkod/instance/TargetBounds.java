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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.instance;

import static java.util.Collections.unmodifiableMap;
import static kodkod.util.ints.Ints.unmodifiableSequence;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.util.ints.SparseSequence;

/**
 * Adapted from {@link kodkod.instance.Bounds}.
 * 
 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model finding
 * @modified Nuno Macedo // [HASLab] temporal model finding
 **/
public class TargetBounds extends Bounds {
	private final Map<Relation, TupleSet> targets;
	private final Map<Relation, Integer> weights;
	
	/**
	 * Constructs a Bounds object with the given factory and mappings.
	 */
	protected TargetBounds(TupleFactory factory, Map<Relation, TupleSet> lower, Map<Relation, TupleSet> upper,
			Map<Relation, TupleSet> target, Map<Relation, Integer> weights, SparseSequence<TupleSet> intbounds) {
		super(factory, lower, upper, intbounds);
		this.weights = weights;
		this.targets = target;
	}

	/**
	 * Constructs new Bounds over the given universe.
	 * 
	 * @ensures this.universe' = universe && no this.relations' && no
	 *          this.intBound'
	 * @throws NullPointerException
	 *             universe = null
	 */
	public TargetBounds(Universe universe) {
		super(universe);
		this.targets = new LinkedHashMap<Relation, TupleSet>();
		this.weights = new LinkedHashMap<Relation, Integer>();
	}

	/**
	 * Returns a set view of the relations mapped by the given lower/upper
	 * bounds.
	 * 
	 * @requires lowers.keySet().equals(uppers.keySet())
	 * @return a set view of the relations mapped by the given lower/upper
	 *         bounds
	 */
	protected static <T extends Relation> Set<T> relations(final Map<T, TupleSet> lowers, final Map<T, TupleSet> uppers) { 
		return new AbstractSet<T>() {

			public Iterator<T> iterator() {
				return new Iterator<T>() {
					final Iterator<T> itr = uppers.keySet().iterator();
					T last = null;

					public boolean hasNext() {
						return itr.hasNext();
					}

					public T next() {
						return last = itr.next();
					}

					public void remove() {
						itr.remove();
						lowers.remove(last);
					}
				};
			}

			public int size() {
				return uppers.size();
			}

			public boolean contains(Object key) {
				return uppers.containsKey(key);
			}

			public boolean remove(Object key) {
				return (uppers.remove(key) != null) && (lowers.remove(key) != null);
			}

			public boolean removeAll(Collection<?> c) {
				return uppers.keySet().removeAll(c) && lowers.keySet().removeAll(c);
			}

			public boolean retainAll(Collection<?> c) {
				return uppers.keySet().retainAll(c) && lowers.keySet().retainAll(c);
			}
		};
	}


	/**
	 * Returns the set of tuples that are the target of r. r may be in
	 * this.relations and not have targets set. If r is not mapped by this, null
	 * is returned.
	 * 
	 * @return r in this.targets.TupleSet => targets[r], null
	 */
	public TupleSet target(Relation r) {
		return targets.get(r);
	}

	/**
	 * Returns a map view of this.targets. The returned map is not modifiable.
	 * 
	 * @return a map view of this.targets
	 */
	public Map<Relation, TupleSet> targets() {
		return unmodifiableMap(targets);
	}

	/**
	 * Returns the weight of r for TO runs. r may be in this.targets and not
	 * have weights set. If r is not mapped by this, null is returned.
	 * 
	 * @return r in this.weights.Int => weights[r], null
	 */
	public Integer weight(Relation r) {
		return weights.get(r);
	}

	/**
	 * Returns a map view of this.weights. The returned map is not modifiable.
	 * 
	 * @return a map view of this.weights
	 */
	public Map<Relation, Integer> weights() {
		return unmodifiableMap(weights);
	}


	/**
	 * Sets the target for the given relation.
	 * 
	 * @requires target in this.upperBound[r] && this.lowerBound[r] in target
	 *           && target.arity = r.arity && target.universe = this.universe &&
	 *           r in this.relations
	 * @ensures this.relations' = this.relations
	 * 		    this.lowerBound' = this.lowerBound
	 * 			this.upperBound' = this.upperBound
	 * 			this.targets' = this.targets ++ r->target
	 * 			this.weights' = this.weights
	 * @throws NullPointerException r = null || target = null
	 * @throws IllegalArgumentException 
	 * 		target.arity != r.arity || upper.universe != this.universe || r !in this.relations || 
	 * 		target !in this.upperBound[r] || this.lowerBound[r] !in target      
	 */
	public void setTarget(Relation r, TupleSet target) {
		if (!relations().contains(r))
			throw new IllegalArgumentException("r !in this.relations");
		if (!upperBounds().get(r).containsAll(target))
			throw new IllegalArgumentException("target.tuples !in upper.tuples");
		if (!target.containsAll(lowerBounds().get(r)))
			throw new IllegalArgumentException("lower.tuples !in target.tuples");
		targets.put(r, target.clone().unmodifiableView());
	}

	/**
	 * Sets the weight for the given relation.
	 * 
	 * @requires r in this.relations
	 * @ensures this.relations' = this.relations
	 * 		    this.lowerBound' = this.lowerBound
	 * 			this.upperBound' = this.upperBound
	 * 			this.targets' = this.targets
	 * 			this.weights' = this.weights ++ r->weight
	 * @throws NullPointerException r = null || weight = null
	 * @throws IllegalArgumentException r !in this.relations
	 */
	public void setWeight(Relation r, Integer weight) {
		// TODO: test range of weight
		if (!relations().contains(r))
			throw new IllegalArgumentException("r !in this.relations");
		weights.put(r, weight);
	}

	/**
	 * Returns an unmodifiable view of this Bounds object.
	 * 
	 * @return an unmodifiable view of his Bounds object.
	 */
	public TargetBounds unmodifiableView() {
		return new TargetBounds(universe().factory(), unmodifiableMap(lowerBounds()), unmodifiableMap(upperBounds()), unmodifiableMap(targets),
				unmodifiableMap(weights), unmodifiableSequence(super.intBounds()));
	}

	/**
	 * Returns a deep (modifiable) copy of this Bounds object.
	 * 
	 * @return a deep (modifiable) copy of this Bounds object.
	 */
	public TargetBounds clone() {
		try {
			return new TargetBounds(universe().factory(), new LinkedHashMap<Relation, TupleSet>(lowerBounds()),
					new LinkedHashMap<Relation, TupleSet>(upperBounds()), new LinkedHashMap<Relation, TupleSet>(targets),
					new LinkedHashMap<Relation, Integer>(weights), intBounds().clone());
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuilder str = new StringBuilder();
		str.append("relation bounds:");
		for (Map.Entry<Relation, TupleSet> entry : lowerBounds().entrySet()) {
			str.append("\n ");
			str.append(entry.getKey());
			str.append(": [");
			str.append(entry.getValue());
			TupleSet upper = upperBounds().get(entry.getKey());
			if (!upper.equals(entry.getValue())) {
				str.append(", ");
				str.append(upper);
			}
			TupleSet target = targets.get(entry.getKey());
			if (!target.isEmpty()) {
				str.append(", ");
				str.append(target);
			}
			str.append("]");
		}
		str.append("\nint bounds: ");
		str.append("\n ");
		str.append(intBounds());
		return str.toString();
	}

}
