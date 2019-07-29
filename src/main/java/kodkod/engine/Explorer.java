package kodkod.engine;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Relation;
import kodkod.instance.TupleSet;

/**
 * An iterator implementing more advanced iteration strategies for temporal
 * solutions.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding, temporal scenario
 *         exploration
 *
 * @param <T> The type to be iterated.
 */
public interface Explorer<T> extends Iterator<T> {

	/**
	 * Produces an alternative solution by iterating over the selected {@code state}
	 * of the trace, fixing all previous states. A set {@code ignore} of relations
	 * can be specified so that their valuations are ignored during iteration.
	 * Iteration may or not {@code exclude} the state at the selected position from
	 * future iterations, and that of higher positions is reset.
	 * 
	 * @param state   the state which will be iterated.
	 * @param ignore  relations whose valuation will be ignored in iteration of 
	 * 				  {@code state}.
	 * @param force   fixed valuations for a set of relations that will be changed
	 *                at {@code state}.
	 * @param exclude whether the current value of the {@code state} is to be
	 *                excluded from future iterations.
	 * @return the next branching solution
	 */
	public T branch(int state, Set<Relation> ignore, Map<Relation, TupleSet> force, boolean exclude);

}
