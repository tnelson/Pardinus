package kodkod.engine;

import java.util.Iterator;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.instance.TupleSet;

/**
 * An iterator implementing more advanced iteration strategies for temporal
 * solutions.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 *
 * @param <T> The type to be iterated.
 */
public interface Explorator<T> extends Iterator<T> {

	/**
	 * Produces an alternative solution by iterating over state i of the trace,
	 * fixing all previous states. Visited i states are accumulated and only reseted
	 * if branching at a lower state.
	 * 
	 * @param i the state which will be iterated.
	 * @return the next branching solution
	 */
	public T branch(int i);

	/**
	 * Produces an alternative solution by forcing a particular valuations for
	 * certain relations for state i of the trace, fixing all previous states and
	 * the values of the other relations at state i. These restrictions are not
	 * accumulated.
	 * 
	 * @param i     the state which will be iterated.
	 * @param force valuations for a set of relations that will be changed at state
	 *              i.
	 * @return the next branching solution
	 */
	public T branch(int i, Map<Relation, TupleSet> force);
	
	/**
	 * Produces an alternative solution by forcing a particular valuations for
	 * certain relations for state i of the trace, fixing all previous states and
	 * the values of the other relations at state i. These restrictions are not
	 * accumulated.
	 * 
	 * @param i    the state which will be iterated.
	 * @param form the formula that will be enforced at state i.
	 * @return the next branching solution
	 */
	public T branch(int i, Formula form);

}
