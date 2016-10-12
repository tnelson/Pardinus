package kodkod.instance;

import static java.util.Collections.unmodifiableMap;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.util.ints.SparseSequence;
import kodkod.util.ints.TreeSequence;

public class RelativeBounds extends Bounds {

	private Map<Relation, Relation[]> lowers = new LinkedHashMap<Relation, Relation[]>();
	private Map<Relation, Relation[]> uppers = new LinkedHashMap<Relation, Relation[]>();
	private final Set<Relation> rel_relations;

	public RelativeBounds(Universe universe) {
		super(universe);
		this.rel_relations = rel_relations(lowers, uppers);
	}

	public RelativeBounds(TupleFactory factory,
			Map<Relation, TupleSet> lowerBounds,
			Map<Relation, TupleSet> upperBounds,
			Map<Relation, Relation[]> linkedHashMap,
			Map<Relation, Relation[]> linkedHashMap2,
			SparseSequence<TupleSet> clone) {
		super(factory, lowerBounds, upperBounds, clone);
		this.lowers = linkedHashMap;
		this.uppers = linkedHashMap2;
		this.rel_relations = rel_relations(lowers, uppers);
	}

	public RelativeBounds(Bounds bounds1) {
		super(bounds1.universe().factory(), new LinkedHashMap<Relation, TupleSet>(bounds1.lowerBounds()), new LinkedHashMap<Relation, TupleSet>(bounds1
				.upperBounds()), new TreeSequence<TupleSet>(bounds1.intBounds()));
		if (bounds1 instanceof RelativeBounds) {
			this.lowers = new LinkedHashMap<Relation, Relation[]>(((RelativeBounds) bounds1).lowerRelBounds());
			this.uppers = new LinkedHashMap<Relation, Relation[]>(((RelativeBounds) bounds1).upperRelBounds());
		}
		this.rel_relations = rel_relations(lowers, uppers);
	}

	public void bound(Relation relation, Relation[] upper) {
		if (upper.length != relation.arity())
			throw new IllegalArgumentException();
		lowers.put(relation, new Relation[relation.arity()]);
		uppers.put(relation, upper);
	}

	public void boundExactly(Relation relation, Relation[] upper) {
		if (upper.length != relation.arity())
			throw new IllegalArgumentException();
		lowers.put(relation, upper);
		uppers.put(relation, upper);
	}

	public void bound(Relation relation, Relation[] lower, Relation[] upper) {
		if (lower.length != relation.arity()
				|| upper.length != relation.arity())
			throw new IllegalArgumentException();
		lowers.put(relation, lower);
		uppers.put(relation, upper);
	}

	public void resolve() {
		for (Relation r : lowers.keySet()) {
			TupleSet aux1 = resolveLower(lowers.get(r)[0]);
			for (int i = 1; i < lowers.get(r).length; i++)
				aux1 = aux1.product(resolveLower(lowers.get(r)[i]));

			TupleSet aux2 = resolveUpper(uppers.get(r)[0]);
			for (int i = 1; i < uppers.get(r).length; i++)
				aux2 = aux2.product(resolveUpper(uppers.get(r)[i]));

			super.bound(r, aux1, aux2);
		}
	}

	private TupleSet resolveLower(Relation r) {
		if (r == null)
			return universe().factory().noneOf(1);
		else
			return super.lowerBound(r);
	}

	private TupleSet resolveUpper(Relation r) {
		if (r == null)
			return universe().factory().noneOf(1);
		else
			return super.upperBound(r);
	}

	public RelativeBounds clone() {
		try {
			return new RelativeBounds(universe().factory(),
					new LinkedHashMap<Relation, TupleSet>(super.lowerBounds()), new LinkedHashMap<Relation, TupleSet>(super.upperBounds()),
					new LinkedHashMap<Relation, Relation[]>(lowers),
					new LinkedHashMap<Relation, Relation[]>(uppers), super
							.intBounds().clone());
		} catch (CloneNotSupportedException cnse) {
			throw new InternalError(); // should not be reached
		}
	}

	protected static <T extends Relation> Set<T> rel_relations(
			final Map<T, Relation[]> lowers, final Map<T, Relation[]> uppers) {
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

	public Set<Relation> relrelations() {
		return rel_relations;
	}

	public Relation[] lowerRelBounds(Relation r) {
		return lowers.get(r);
	}

	public Relation[] upperRelBounds(Relation r) {
		return uppers.get(r);
	}
	
	public Map<Relation, Relation[]> lowerRelBounds() {
		return unmodifiableMap(lowers);
	}

	public Map<Relation, Relation[]> upperRelBounds() {
		return unmodifiableMap(uppers);
	}
}
