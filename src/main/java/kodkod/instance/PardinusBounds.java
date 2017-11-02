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
import static java.util.Collections.unmodifiableMap;
import static kodkod.util.ints.Ints.unmodifiableSequence;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.fol2sat.RelationCollector;
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
 * Adapted from {@link kodkod.instance.Bounds}.
 * 
 * @author Nuno Macedo // [HASLab] temporal, decomposed, symbolic model finding
 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented model
 *         finding
 */
public class PardinusBounds extends Bounds {

	/* Symbolic bounds */

	private final Map<Relation, Expression> lowers_symb;
	private final Map<Relation, Expression> uppers_symb;
	private final Set<Relation> relations_symb;

	/* Target-oriented bounds */

	private final Map<Relation, TupleSet> targets;
	private final Map<Relation, Integer> weights;

	/* Temporal bounds */

	/**
	 * Store the lower and upper bounds for the variable relations in each
	 * position of the bound trace.
	 */
	private final List<Map<VarRelation, TupleSet>> uppers_trace;
	private final List<Map<VarRelation, TupleSet>> lowers_trace;
	private final List<Set<VarRelation>> relations_vars;

	// TODO: guarantee that the same relations are bound for every step
	
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
	private int loop;

	/* Decomposed bounds */

	private boolean integrated;
	private PardinusBounds amalgamated;
	public Instance config;
	public boolean trivial_config;

	/* Constructors */

	/**
	 * Constructs new empty bounds over the given universe.
	 * 
	 * @ensures this.universe' = universe && no this.relations' && no
	 *          this.intBound'
	 * @throws NullPointerException
	 *             universe = null
	 */
	public PardinusBounds(Universe universe) {
		super(universe);
		this.targets = new LinkedHashMap<Relation, TupleSet>();
		this.weights = new LinkedHashMap<Relation, Integer>();
		this.uppers_trace = new ArrayList<Map<VarRelation, TupleSet>>();
		this.lowers_trace = new ArrayList<Map<VarRelation, TupleSet>>();
		this.relations_vars = relations(this.lowers_trace, this.uppers_trace);
		this.loop = 0;
		this.amalgamated = null;
		this.trivial_config = false;
		this.integrated = false;
		this.lowers_symb = new LinkedHashMap<Relation, Expression>();
		this.uppers_symb = new LinkedHashMap<Relation, Expression>();
		this.relations_symb = symb_relations(lowers_symb, uppers_symb);
		this.symbolic = new SymbolicStructures();
		add();
	}

	/**
	 * Constructs new complete bounds over the given universe.
	 * 
	 * @ensures this.universe' = universe && no this.relations' && no
	 *          this.intBound' && ...
	 * @throws NullPointerException
	 *             universe = null
	 */
	private PardinusBounds(TupleFactory factory,
			Map<Relation, TupleSet> lower, Map<Relation, TupleSet> upper,
			List<Map<VarRelation, TupleSet>> lowers_t,
			List<Map<VarRelation, TupleSet>> uppers_t, int loop,
			Map<Relation, TupleSet> target, Map<Relation, Integer> weights,
			Map<Relation, Expression> lowers_s,
			Map<Relation, Expression> uppers_s, SymbolicStructures symbolic,
			SparseSequence<TupleSet> intbounds, PardinusBounds amalg,
			boolean integrated, boolean trivial_config, Instance config) {
		super(factory, lower, upper, intbounds);
		this.targets = target;
		this.weights = weights;
		this.uppers_trace = uppers_t;
		this.lowers_trace = lowers_t;
		this.loop = loop;
		this.relations_vars = relations(this.lowers_trace, this.uppers_trace);
		this.amalgamated = amalg;
		this.trivial_config = trivial_config;
		this.integrated = integrated;
		this.lowers_symb = lowers_s;
		this.uppers_symb = uppers_s;
		this.symbolic = new SymbolicStructures(symbolic.reif,symbolic.dereif,symbolic.deps);
		this.relations_symb = symb_relations(lowers_symb, uppers_symb);
		this.config = config;
	}

	/**
	 * Constructor for decomposed bounds. The first is the partial problem
	 * (which will be encoded in this) and the second is amalgamated with the
	 * first in amalgamated. Non-mergeable data is selected from <partial>.
	 * 
	 * @param partial
	 * @param remainder
	 */
	public PardinusBounds(PardinusBounds partial, Bounds remainder) {
		this(partial.universe().factory(), partial.lowerBounds(), partial
				.upperBounds(), partial.lowers_trace, partial.uppers_trace,
				partial.loop(), partial.targets, partial.weights,
				partial.lowers_symb, partial.uppers_symb, partial.symbolic, partial.intBounds(),
				null, partial.integrated, partial.trivial_config,partial.config);

		// TODO: trace bounds are not being correctly assigned
		
		this.amalgamated = partial.clone();
		this.amalgamated.merge(remainder);
	}
	
	public PardinusBounds(PardinusBounds partial, boolean x) {
		this(partial.universe().factory(), new HashMap<Relation, TupleSet>(), new HashMap<Relation, TupleSet>(), 
				new ArrayList<Map<VarRelation, TupleSet>>(), new ArrayList<Map<VarRelation, TupleSet>>(),
				0, partial.targets, partial.weights,
				partial.lowers_symb, partial.uppers_symb, partial.symbolic, partial.intBounds(),
				null, partial.integrated, partial.trivial_config,partial.config);

		current = 0;
		add();
		
		for (Relation r : partial.relations())
			if (!(r instanceof VarRelation))
				this.bound(r,partial.lowerBound(r),partial.upperBound(r));
		
		// TODO: trace bounds are not being correctly assigned
		
		this.amalgamated = partial.clone();
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
		final TupleSet unmodifiableTuplesCopy = tuples.clone()
				.unmodifiableView();
		lowers_trace.get(current).put((VarRelation) r, unmodifiableTuplesCopy);
		uppers_trace.get(current).put((VarRelation) r, unmodifiableTuplesCopy);
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
			lowers_trace.get(current).put((VarRelation) r,
					lower.clone().unmodifiableView());
			uppers_trace.get(current).put((VarRelation) r,
					upper.clone().unmodifiableView());
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
		lowers_trace.get(current).put((VarRelation) r,
				universe().factory().noneOf(r.arity()).unmodifiableView());
		uppers_trace.get(current).put((VarRelation) r,
				upper.clone().unmodifiableView());
	}

	/**
	 * The set of relations defined in the succeeding position of the trace
	 * bound. This includes every previously bound static relation and the
	 * variable ones bound in this position.
	 */
	@Override
	public Set<Relation> relations() {
		Set<Relation> aux = new HashSet<Relation>(relations_vars.get(current));
		aux.addAll(super.relations());
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
			return lowers_trace.get(current).get(r);
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
		Map<Relation, TupleSet> aux = new HashMap<Relation, TupleSet>(
				lowers_trace.get(current));
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
			return uppers_trace.get(current).get(r);
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
		Map<Relation, TupleSet> aux = new HashMap<Relation, TupleSet>(
				uppers_trace.get(current));
		aux.putAll(super.upperBounds());
		return aux;
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
	 * @requires target in this.upperBound[r] && this.lowerBound[r] in target &&
	 *           target.arity = r.arity && target.universe = this.universe && r
	 *           in this.relations
	 * @ensures this.relations' = this.relations this.lowerBound' =
	 *          this.lowerBound this.upperBound' = this.upperBound this.targets'
	 *          = this.targets ++ r->target this.weights' = this.weights
	 * @throws NullPointerException
	 *             r = null || target = null
	 * @throws IllegalArgumentException
	 *             target.arity != r.arity || upper.universe != this.universe ||
	 *             r !in this.relations || target !in this.upperBound[r] ||
	 *             this.lowerBound[r] !in target
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
	 * @ensures this.relations' = this.relations this.lowerBound' =
	 *          this.lowerBound this.upperBound' = this.upperBound this.targets'
	 *          = this.targets this.weights' = this.weights ++ r->weight
	 * @throws NullPointerException
	 *             r = null || weight = null
	 * @throws IllegalArgumentException
	 *             r !in this.relations
	 */
	public void setWeight(Relation r, Integer weight) {
		// TODO: test range of weight
		if (!relations().contains(r))
			throw new IllegalArgumentException("r !in this.relations");
		weights.put(r, weight);
	}

	public PardinusBounds amalgamated() {
		return amalgamated;
	}

	public boolean integrated() {
		return integrated;
	}
	
	public PardinusBounds integrated(Solution sol) {
		if (integrated)
			throw new IllegalArgumentException("Already integrated.");
		if (amalgamated == null)
			throw new IllegalArgumentException("Not decomposed bounds.");
		if (!sol.sat())
			throw new IllegalArgumentException("Can't integrate unsat.");

		
		PardinusBounds integrated = amalgamated.clone();
		integrated.config = sol.instance();

		if (sol.stats().primaryVariables() == 0)
			trivial_config = true;

		for (Relation e : this.relations()) {
			if (getTupleConfiguration(e.name(), sol.instance()) != null) {
				integrated.boundExactly(e,
						getTupleConfiguration(e.name(), sol.instance()));
			}
		}

		integrated.amalgamated = this.amalgamated;
		integrated.trivial_config = this.trivial_config;
		integrated.integrated = true;
		
		return integrated;
	}

	private static TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet()) {
			if (r.name().equals(name)) {
				return s.relationTuples().get(r);
			}
		}
		return null;
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
		current = current < uppers_trace.size() - 1 ? current + 1 : loop;
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

	public void first() {
		current = 0;
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
		lowers_trace.remove(current);
		uppers_trace.remove(current);
		relations_vars.remove(current);
	}

	/**
	 * Adds a new bounds in the current position of the iterator, between its
	 * next and previous positions.
	 */
	public void add() {
		Map<VarRelation, TupleSet> lowers = new HashMap<VarRelation, TupleSet>();
		Map<VarRelation, TupleSet> uppers = new HashMap<VarRelation, TupleSet>();
		this.lowers_trace.add(current, lowers);
		this.uppers_trace.add(current, uppers);
		this.relations_vars.add(current,
				(Set<VarRelation>) Bounds.relations(lowers, uppers));
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
	 * The set of variable relations defined in the succeeding position of the
	 * trace bound, i.e., variable relations bound in this position.
	 */
	@Deprecated
	public Set<VarRelation> varRelations() {
		Set<VarRelation> aux = new HashSet<VarRelation>(
				relations_vars.get(current));
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
	private static List<Set<VarRelation>> relations(
			List<Map<VarRelation, TupleSet>> lowers,
			List<Map<VarRelation, TupleSet>> uppers) {
		List<Set<VarRelation>> relations = new ArrayList<Set<VarRelation>>();
		for (int i = 0; i < uppers.size(); i++) {
			relations.add((Set<VarRelation>) Bounds.relations(lowers.get(i),
					uppers.get(i)));
		}
		return relations;
	}

	public List<Set<VarRelation>> relationsVars() {
		return relations_vars;
	}

	public void bound(Relation relation, Expression upper) {
		Expression r = ConstantExpression.NONE;
		for (int i = 1; i < relation.arity(); i++)
			r = r.product(ConstantExpression.NONE);

		symbolic.checkBound(relation, upper);
		lowers_symb.put(relation, r);
		uppers_symb.put(relation, upper);
	}

	public void boundExactly(Relation relation, Expression upper) {
		symbolic.checkBound(relation, upper);
		lowers_symb.put(relation, upper);
		uppers_symb.put(relation, upper);
	}

	public void bound(Relation relation, Expression lower, Expression upper) {
		symbolic.checkBound(relation, lower.union(upper));
		lowers_symb.put(relation, lower);
		uppers_symb.put(relation, upper);
	}

	private final SymbolicStructures symbolic;
	
	public Formula resolve() {
		Formula xtra = ConstantFormula.TRUE;
		for (Relation r : relations_symb) {
			if (super.relations().contains(r)
					&& super.lowerBound(r).size() == super.upperBound(r).size())
				continue;
			TupleSet aux1 = symbolic.resolveLower(lowers_symb.get(r));
			TupleSet aux2 = symbolic.resolveUpper(uppers_symb.get(r));
			if (super.lowerBound(r) != null) {
				if (!aux1.containsAll(super.lowerBound(r)))
					return Formula.FALSE;
				if (!super.lowerBound(r).containsAll(aux2))
					return Formula.FALSE;
			}
			super.bound(r, aux1, aux2);
			if (aux1.size() != aux2.size())
				xtra = xtra.and(lowers_symb.get(r).in(r)).and(r.in(uppers_symb.get(r)));
		}
		relations_symb.clear();
		return xtra;
	}

	/**
	 * Tests whether this bounds must be resolved.
	 * @return whether this needs resolving.
	 */
	public boolean resolved() {
		return relations_symb.isEmpty();
	}

	/**
	 * Given a tuple set, returns an expression representing it by composing the
	 * relations that reify each atom, as stored in the <symbolic> structure.
	 * This is needed to specify symbolic bounds that mix both expressions and
	 * particular atoms.
	 * 
	 * @param tset
	 *            the tuple set to be reified.
	 * @return the resulting expresion.
	 */
	public Expression reify(TupleSet tset) {
		Expression r = ConstantExpression.NONE;
		for (int i = 1; i < tset.arity(); i++)
			r = r.product(ConstantExpression.NONE);
		
		Iterator<Tuple> it = tset.iterator();
		while (it.hasNext()) {
			Tuple u = it.next();
			Expression r1 = symbolic.reif.get(u.atom(0));
			for (int i = 1; i < u.arity(); i ++)
				r1 = r1.product(symbolic.reif.get(u.atom(i)));
			r = r.union(r1);
		}
		return r;
	}

	private static <T extends Relation> Set<T> symb_relations(
			final Map<T, Expression> lowers, final Map<T, Expression> uppers) {
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
				return (uppers.remove(key) != null)
						&& (lowers.remove(key) != null);
			}

			public boolean removeAll(Collection<?> c) {
				return uppers.keySet().removeAll(c)
						&& lowers.keySet().removeAll(c);
			}

			public boolean retainAll(Collection<?> c) {
				return uppers.keySet().retainAll(c)
						&& lowers.keySet().retainAll(c);
			}
		};
	}

	public Set<Relation> relationsSymb() {
		return relations_symb;
	}

	public Expression lowerSymbBounds(Relation r) {
		return lowers_symb.get(r);
	}

	public Expression upperSymbBounds(Relation r) {
		return uppers_symb.get(r);
	}

	public Map<Relation, Expression> lowerSymbBounds() {
		return unmodifiableMap(lowers_symb);
	}

	public Map<Relation, Expression> upperSymbBounds() {
		return unmodifiableMap(uppers_symb);
	}

	/**
	 * Merges the information of another Bounds object into <this>.
	 * Non-mergeable data is overridden.
	 * 
	 * @param bounds
	 *            the bounds to be merged.
	 */
	public void merge(Bounds bounds) {
		for (Relation r : bounds.relations())
			this.bound(r, bounds.lowerBound(r),bounds.upperBound(r));
		if (bounds instanceof PardinusBounds) {
			PardinusBounds bnds = (PardinusBounds) bounds;
			for (Relation r : bnds.relationsSymb())
				this.bound(r, bnds.lowerSymbBounds(r), bnds.upperSymbBounds(r));
			for (int i = 0; i < bnds.relationsVars().size(); i++) {
				for (VarRelation r : bnds.relationsVars().get(i))
					this.bound(r, bnds.lowers_trace.get(i).get(r),
							bnds.uppers_trace.get(i).get(r));
			}
			for (Relation r : bounds.relations()) {
				if (bnds.target(r) != null)
					this.setTarget(r, bnds.target(r));
				if (bnds.weight(r) != null)
					this.setWeight(r, bnds.weight(r));
			}
			this.symbolic.merge(bnds.symbolic);
			this.integrated = bnds.integrated;
			this.loop = bnds.loop;
			this.trivial_config = bnds.trivial_config;
		}	
	}

	/**
	 * {@inheritDoc}
	 */
	public PardinusBounds unmodifiableView() {
		return new PardinusBounds(universe().factory(),
				super.lowerBounds(), super.upperBounds(),
				unmodifiableList(lowers_trace), unmodifiableList(uppers_trace), loop,
				unmodifiableMap(targets), unmodifiableMap(weights),
				unmodifiableMap(lowers_symb), unmodifiableMap(uppers_symb),
				symbolic.unmodifiableView(), unmodifiableSequence(super.intBounds()),
				amalgamated==null?null:amalgamated.unmodifiableView(), integrated, trivial_config,config);
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public PardinusBounds clone() {
		try {
			List<Map<VarRelation, TupleSet>> l1 = new ArrayList<Map<VarRelation, TupleSet>>();
			List<Map<VarRelation, TupleSet>> l2 = new ArrayList<Map<VarRelation, TupleSet>>();
			for (int i = 0; i < lowers_trace.size(); i++) {
				l1.add(new LinkedHashMap<VarRelation, TupleSet>(lowers_trace.get(i)));
				l2.add(new LinkedHashMap<VarRelation, TupleSet>(uppers_trace.get(i)));
			}
				
			return new PardinusBounds(universe().factory(),
					new LinkedHashMap<Relation, TupleSet>(super.lowerBounds()),
					new LinkedHashMap<Relation, TupleSet>(super.upperBounds()),
					l1,l2,loop,
					new LinkedHashMap<Relation, TupleSet>(targets),
					new LinkedHashMap<Relation, Integer>(weights),
					new LinkedHashMap<Relation, Expression>(lowers_symb),
					new LinkedHashMap<Relation, Expression>(uppers_symb),
					symbolic.clone(),
					super.intBounds().clone(), amalgamated == null?null:amalgamated.clone(),
					integrated, trivial_config,config);
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public String toString() {
		final StringBuilder str = new StringBuilder();
		str.append("static relation bounds:");
		for (Map.Entry<Relation, TupleSet> entry : super.lowerBounds()
				.entrySet()) {
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
		str.append("\nsymbolic static relation bounds:");
		for (Entry<Relation, Expression> entry : this.lowerSymbBounds().entrySet()) {
			str.append("\n ");
			str.append(entry.getKey());
			str.append(": [");
			str.append(entry.getValue());
			Expression upper = this.upperSymbBounds().get(entry.getKey());
			if (!upper.equals(entry.getValue())) {
				str.append(", ");
				str.append(upper);
			}
			str.append("]");
		}
		for (int i = 0; i < lowers_trace.size(); i++) {
			str.append("\nvariable relation bounds at " + i + ":");
			for (Map.Entry<VarRelation, TupleSet> entry : lowers_trace.get(i)
					.entrySet()) {
				str.append("\n ");
				str.append(entry.getKey());
				str.append(": [");
				str.append(entry.getValue());
				TupleSet upper = uppers_trace.get(i).get(entry.getKey());
				if (!upper.equals(entry.getValue())) {
					str.append(", ");
					str.append(upper);
				}
				TupleSet target = targets.get(entry.getKey());
				if (target != null && !target.isEmpty()) {
					str.append(", ");
					str.append(target);
				}
				str.append("]");
			}
		}
		str.append("\nint bounds: ");
		str.append(intBounds());
		str.append("\nloop: ");
		str.append(loop);
		if (amalgamated!=null) {
			str.append("\namalgamated:\n\t");
			str.append(amalgamated.toString().replace("\n", "\n\t"));
		}
		return str.toString();
	}
	
	/**
	 * A class that stores information relevant for handling symbolic bounds.
	 * This includes a relation that reifies every atom of the universe, and the
	 * dependencies of these symbolic bounds found thus far.
	 */
	private class SymbolicStructures {
		private final Map<Object,Relation> reif;
		private final Map<Relation,TupleSet> dereif;
		private final Map<Relation,Set<Relation>> deps;

		/**
		 * Initializes the symbolic structures, by reifying every atom of the
		 * universe.
		 */
		private SymbolicStructures() {
			reif = new HashMap<Object, Relation>();
			dereif = new HashMap<Relation, TupleSet>();
			deps = new HashMap<Relation, Set<Relation>>();
			for (int i = 0; i < universe().size(); i++) {
				Relation r = Relation.unary(universe().atom(i).toString());
				reif.put(universe().atom(i), r);
				dereif.put(r, universe().factory().setOf(universe().atom(i)));
			}
		}
		
		/**
		 * Creates a symbolic structure with non-empty information.
		 * 
		 * @param reif
		 *            the relation that reifies each atom.
		 * @param dereif
		 *            the relation that dereifies each relation.
		 * @param deps
		 *            the direct dependencies of symbolically bound relation.
		 */
		private SymbolicStructures(Map<Object, Relation> reif,
				Map<Relation, TupleSet> dereif,
				Map<Relation, Set<Relation>> deps) {
			this.reif = reif;
			this.dereif = dereif;
			this.deps = deps;
		}

		/**
		 * Checks whether an expression is a valid symbolic bound for a given
		 * relation. Will fail if incorrect arity or cyclic dependency.
		 * 
		 * @param relation
		 *            the relation to be symbolically bound.
		 * @param bound
		 *            the symbolic bound.
		 * @throws IllegalArgumentException bound.arity != r.arity
		 * @throws IllegalArgumentException r in *deps(bounds)
		 */
		private void checkBound(Relation relation, Expression bound) {
			if (relation.arity() != bound.arity())
				throw new IllegalArgumentException("bound.arity != r.arity");
			RelationCollector col = new RelationCollector(new HashSet<Node>());
			Set<Relation> rs = bound.accept(col);
			deps.put(relation, rs);
			rs = transitiveDeps(rs);
			if (rs.contains(relation))
				throw new IllegalArgumentException("r in *deps(bounds)");
		}

		/**
		 * Calculates the reflexive-transitive dependencies of a set of
		 * relations.
		 * 
		 * @param rs
		 *            the relations for which to calculate the dependencies.
		 * @return the transitive dependencies.
		 */
		private Set<Relation> transitiveDeps(Set<Relation> rs) {
			Set<Relation> ds = new HashSet<Relation>(rs);
			
			for (Relation r : rs) {
				Set<Relation> aux = deps.get(r);
				if (aux != null)
					ds.addAll(transitiveDeps(aux));
			}
			
			return ds;
		}

		/**
		 * Given the current constant bounds, resolves the lower symbolic bounds
		 * of a relation.
		 * 
		 * TODO: recursively resolve.
		 * 
		 * @param bound
		 *            the bound to be resolved.
		 * @return the corresponding tuple set.
		 */
		private TupleSet resolveLower(Expression bound) {
			Map<Relation,TupleSet> us = new HashMap<Relation, TupleSet>();
			us.putAll(lowers);
			us.putAll(dereif);
			Instance i = new Instance(universe(), lowers, intBounds());
			Evaluator eval = new Evaluator(i);
			return eval.evaluate(bound);
		}

		/**
		 * Given the current constant bounds, resolves the upper symbolic bounds
		 * of a relation.
		 * 
		 * TODO: recursively resolve.
		 * 
		 * @param bound
		 *            the bound to be resolved.
		 * @return the corresponding tuple set.
		 */
		private TupleSet resolveUpper(Expression e) {
			Map<Relation,TupleSet> us = new HashMap<Relation, TupleSet>();
			us.putAll(uppers);
			us.putAll(dereif);
			Instance i = new Instance(universe(), uppers, intBounds());
			Evaluator eval = new Evaluator(i);
			return eval.evaluate(e);
		}

		/**
		 * Merges a symbolic structure into <this>.
		 * 
		 * @param symbolic
		 *            the structure to be merge.
		 */
		public void merge(SymbolicStructures symbolic) {
			reif.putAll(symbolic.reif);
			dereif.putAll(symbolic.dereif);
			deps.putAll(symbolic.deps);
		}

		/**
		 * A (deep) clone of this symbolic structure.
		 * 
		 * @return the clone.
		 */
		public SymbolicStructures clone() {
			return new SymbolicStructures(
					new HashMap<Object, Relation>(reif),
					new HashMap<Relation, TupleSet>(dereif),
					new HashMap<Relation, Set<Relation>>(deps));
		}

		/**
		 * Returns an unmodifiable view of this symbolic structure.
		 * 
		 * @return the unmodifiable view.
		 */
		public SymbolicStructures unmodifiableView() {
			return new SymbolicStructures(
					unmodifiableMap(reif),
					unmodifiableMap(dereif), 
					unmodifiableMap(deps));
		}
	}

}
