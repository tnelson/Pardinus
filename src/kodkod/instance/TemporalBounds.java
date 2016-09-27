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

import static java.util.Collections.unmodifiableList;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.util.ints.SparseSequence;

/**
 * A structure representing the bounds of a temporal model finding problem, that
 * are used to embody partial knowledge about the problem. These temporal bounds
 * are essentially a stream (i.e., infinite sequence) of regular bounds. To be
 * encoded into a finite structure, it is modeled as a finite prefix with a loop
 * pointing to a previous position. Thus, a temporal bound can be used to bind
 * problems with an arbitrary number of states by unrolling the stream. Note
 * that the actual number of states used by the model finder to solve the
 * temporal problem is not known at the time of bound definition. The bounds of
 * static (non-variable) need only be defined once since they do not vary from
 * state to state.
 * 
 * If these temporal bounds are treated like regular bounds (i.e., without ever
 * moving the iterator), then those bounds are applied to every state in the
 * model finding problem (since there is only one position pointing to itself
 * through the loop), behaving as expected from regular bounds.
 * 
 * The same set of variable relations should be bound by every position of the
 * bound trace, otherwise the solving procedure will fail.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalBounds extends Bounds {

	/**
	 * Store the lower and upper bounds for the variable relations in each
	 * position of the bound trace.
	 */
	private final List<Map<VarRelation, TupleSet>> uppers;
	private final List<Map<VarRelation, TupleSet>> lowers;
	private final List<Set<VarRelation>> relations;

	/**
	 * The current (virtual) position of the iterator in the bound trace (not
	 * necessarily the most recent one), sitting between the previous and next
	 * position.
	 */
	private int current = 0;

	/**
	 * The loop of the bound trace, i.e., the position to which the iterator
	 * moves after the last position of the finite prefix.
	 */
	private int loop = 0;

	/**
	 * Constructs a temporal bound trace by copy, with the given factory and
	 * mappings, both for the static and variable relations of the problem.
	 * 
	 * @param factory
	 *            the tuple factory for the bounds.
	 * @param lower
	 *            the lower bounds of the static relations.
	 * @param upper
	 *            the upper bounds of the static relations.
	 * @param lowers
	 *            the lower bounds of the variable relations, by position of the
	 *            trace.
	 * @param uppers
	 *            the upper bounds of the variable relations, by position of the
	 *            trace.
	 * @param intbounds
	 *            the integer bounds.
	 */
	private TemporalBounds(TupleFactory factory, Map<Relation, TupleSet> lower, Map<Relation, TupleSet> upper,
			List<Map<VarRelation, TupleSet>> lowers, List<Map<VarRelation, TupleSet>> uppers,
			SparseSequence<TupleSet> intbounds) {
		super(factory, lower, upper, intbounds);
		this.uppers = uppers;
		this.lowers = lowers;
		this.relations = relations(lowers, uppers);
	}

	/**
	 * Constructs new temporal bounds trace with the given universe.
	 * 
	 * @param universe
	 *            the atom universe.
	 */
	public TemporalBounds(Universe universe) {
		super(universe);
		this.uppers = new ArrayList<Map<VarRelation, TupleSet>>();
		this.lowers = new ArrayList<Map<VarRelation, TupleSet>>();
		this.relations = new ArrayList<Set<VarRelation>>();
		add();
	}

	/**
	 * Whether there is a next position in the bound trace. The trace is assumed
	 * to be infinite, since a loop position is always defined.
	 * 
	 * @return true.
	 */
	public boolean hasNext() {
		return true;
	}

	/**
	 * Moves the iterator forward. It goes back to the loop position if the last
	 * position of the finite prefix trace is the previous position.
	 */
	public void next() {
		current = current < uppers.size() - 1 ? current + 1 : loop;
	}

	/**
	 * Whether there is a previous position in the bound trace. Only false if
	 * the first position is the next position.
	 * 
	 * @return whether there is a previous position.
	 */
	public boolean hasPrevious() {
		return current > 0;
	}

	/**
	 * Moves the iterator backward. Only the finite prefix trace is considered,
	 * the loop is ignored.
	 * 
	 * @throws NoSuchElementException
	 *             if there is no previous position.
	 */
	public void previous() {
		if (hasPrevious())
			current--;
		else
			throw new NoSuchElementException();
	}

	/**
	 * The position succeeding the (virtual) position of the iterator.
	 * 
	 * @return the succeeding position.
	 */
	public int nextIndex() {
		return current;
	}

	/**
	 * The position preceding the (virtual) position of the iterator.
	 * 
	 * @return the preceding position.
	 * @throws NoSuchElementException
	 *             if there is no previous position.
	 */
	public int previousIndex() {
		if (hasPrevious())
			return current - 1;
		else
			throw new NoSuchElementException();
	}

	/**
	 * Removes the bound in the position succeeding the iterator from the trace.
	 */
	public void remove() {
		lowers.remove(current);
		uppers.remove(current);
		relations.remove(current);
	}

	/**
	 * Adds a new bounds in the current position of the iterator, between its
	 * next and previous positions.
	 */
	public void add() {
		Map<VarRelation, TupleSet> lowers = new HashMap<VarRelation, TupleSet>();
		Map<VarRelation, TupleSet> uppers = new HashMap<VarRelation, TupleSet>();
		this.lowers.add(current, lowers);
		this.uppers.add(current, uppers);
		this.relations.add(current, (Set<VarRelation>) Bounds.relations(lowers, uppers));
	}

	/**
	 * The position to which the trace loops after the finite prefix.
	 * 
	 * @return the loop position.
	 */
	public int loop() {
		return loop;
	}

	/**
	 * Updates the position to which the trace loops after the finite prefix.
	 * 
	 * @param loop
	 *            the new loop position.
	 */
	public void setLoop(int loop) {
		this.loop = loop;
	}

	/**
	 * Exactly bounds a relation with a given tuple set in the next position of
	 * the trace bound, if a variable relation. If the relation is static,
	 * relies on the structures of the parent bounds.
	 * 
	 * @see Bounds#boundExactly(Relation, TupleSet)
	 */
	@Override
	public void boundExactly(Relation r, TupleSet tuples) {
		if (!(r instanceof VarRelation)) {
			super.boundExactly(r, tuples);
			return;
		}
		checkBound(r.arity(), tuples);
		final TupleSet unmodifiableTuplesCopy = tuples.clone().unmodifiableView();
		lowers.get(current).put((VarRelation) r, unmodifiableTuplesCopy);
		uppers.get(current).put((VarRelation) r, unmodifiableTuplesCopy);
	}

	/**
	 * Bounds a relation with a pair of given tuple sets in the next position of
	 * the trace bound, if a variable relation. If the relation is static,
	 * relies on the structures of the parent bounds.
	 * 
	 * @see Bounds#bound(Relation, TupleSet)
	 */
	@Override
	public void bound(Relation r, TupleSet lower, TupleSet upper) {
		if (!(r instanceof VarRelation)) {
			super.bound(r, lower, upper);
			return;
		}
		if (!upper.containsAll(lower))
			throw new IllegalArgumentException("lower.tuples !in upper.tuples");
		if (upper.size() == lower.size()) {
			// upper.containsAll(lower) && upper.size()==lower.size() =>
			// upper.equals(lower)
			boundExactly(r, lower);
		} else {
			checkBound(r.arity(), lower);
			checkBound(r.arity(), upper);
			lowers.get(current).put((VarRelation) r, lower.clone().unmodifiableView());
			uppers.get(current).put((VarRelation) r, upper.clone().unmodifiableView());
		}
	}

	/**
	 * Bounds a relation with a given tuple set in the next position of the
	 * trace bound, if a variable relation. If the relation is static, relies on
	 * the structures of the parent bounds.
	 * 
	 * @see Bounds#bound(Relation, TupleSet)
	 */
	@Override
	public void bound(Relation r, TupleSet upper) {
		if (!(r instanceof VarRelation)) {
			super.bound(r, upper);
			return;
		}
		checkBound(r.arity(), upper);
		lowers.get(current).put((VarRelation) r, universe().factory().noneOf(r.arity()).unmodifiableView());
		uppers.get(current).put((VarRelation) r, upper.clone().unmodifiableView());
	}

	/**
	 * The set of relations defined in the succeeding position of the trace
	 * bound. This includes every previously bound static relation and the
	 * variable ones bound in this position.
	 */
	@Override
	public Set<Relation> relations() {
		Set<Relation> aux = new HashSet<Relation>(relations.get(current));
		aux.addAll(super.relations());
		return aux;
	}

	/**
	 * The set of variable relations defined in the succeeding position of the
	 * trace bound, i.e., variable relations bound in this position.
	 */
	public Set<VarRelation> varRelations() {
		Set<VarRelation> aux = new HashSet<VarRelation>(relations.get(current));
		return aux;
	}

	/**
	 * Retrieves a lower bound of a relation. If variable, retrieves its lower
	 * bound at the next position of the bound trace.
	 * 
	 * @see Bounds#lowerBound(Relation)
	 */
	@Override
	public TupleSet lowerBound(Relation r) {
		if (r instanceof VarRelation)
			return lowers.get(current).get(r);
		else
			return super.lowerBound(r);
	}

	/**
	 * Retrieves the defined lower bounds. For variable relations, retrieves
	 * their lower bound at the next position of the bound trace.
	 * 
	 * @see Bounds#lowerBounds()
	 */
	@Override
	public Map<Relation, TupleSet> lowerBounds() {
		Map<Relation, TupleSet> aux = new HashMap<Relation, TupleSet>(lowers.get(current));
		aux.putAll(super.lowerBounds());
		return aux;
	}

	/**
	 * Retrieves an upper bound of a relation. If variable, retrieves its upper
	 * bound at the next position of the bound trace.
	 * 
	 * @see Bounds#upperBound(Relation)
	 */
	@Override
	public TupleSet upperBound(Relation r) {
		if (r instanceof VarRelation)
			return uppers.get(current).get(r);
		else
			return super.upperBound(r);
	}

	/**
	 * Retrieves the defined upper bounds. For variable relations, retrieves
	 * their upper bound at the next position of the bound trace.
	 * 
	 * @see Bounds#upperBounds()
	 */
	@Override
	public Map<Relation, TupleSet> upperBounds() {
		Map<Relation, TupleSet> aux = new HashMap<Relation, TupleSet>(uppers.get(current));
		aux.putAll(super.upperBounds());
		return aux;
	}

	/**
	 * Binds, at each position of the trace, the set of relations defined in the
	 * upper and lower bounds.
	 * 
	 * @param lowers
	 *            the lower bounds.
	 * @param uppers
	 *            the upper bounds.
	 * @return the relations defined by the bounds at each position.
	 */
	private static List<Set<VarRelation>> relations(List<Map<VarRelation, TupleSet>> lowers,
			List<Map<VarRelation, TupleSet>> uppers) {
		List<Set<VarRelation>> relations = new ArrayList<Set<VarRelation>>();
		for (int i = 0; i < uppers.size(); i++) {
			relations.add((Set<VarRelation>) Bounds.relations(lowers.get(i), uppers.get(i)));
		}
		return relations;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see Bounds#unmodifiableView()
	 */
	public TemporalBounds unmodifiableView() {
		return new TemporalBounds(universe().factory(), super.lowerBounds(), super.upperBounds(),
				unmodifiableList(lowers), unmodifiableList(uppers), super.intBounds());
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see Bounds#clone()
	 */
	public TemporalBounds clone() {
		try {
			return new TemporalBounds(universe().factory(), new LinkedHashMap<Relation, TupleSet>(super.lowerBounds()),
					new LinkedHashMap<Relation, TupleSet>(super.upperBounds()),
					new ArrayList<Map<VarRelation, TupleSet>>(lowers),
					new ArrayList<Map<VarRelation, TupleSet>>(uppers), super.intBounds().clone());
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuilder str = new StringBuilder();
		str.append("static relation bounds:");
		for (Map.Entry<Relation, TupleSet> entry : super.lowerBounds().entrySet()) {
			str.append("\n ");
			str.append(entry.getKey());
			str.append(": [");
			str.append(entry.getValue());
			TupleSet upper = super.upperBounds().get(entry.getKey());
			if (!upper.equals(entry.getValue())) {
				str.append(", ");
				str.append(upper);
			}
			str.append("]");
		}
		for (int i = 0; i < lowers.size(); i++) {
			str.append("\nvariable relation bounds at " + i + ":");
			for (Map.Entry<VarRelation, TupleSet> entry : lowers.get(i).entrySet()) {
				str.append("\n ");
				str.append(entry.getKey());
				str.append(": [");
				str.append(entry.getValue());
				TupleSet upper = uppers.get(i).get(entry.getKey());
				if (!upper.equals(entry.getValue())) {
					str.append(", ");
					str.append(upper);
				}
				str.append("]");
			}
		}
		str.append("\nint bounds: ");
		str.append("\n ");
		str.append(intBounds());
		str.append("\nloop: ");
		str.append("\n ");
		str.append(loop);
		return str.toString();
	}

}
