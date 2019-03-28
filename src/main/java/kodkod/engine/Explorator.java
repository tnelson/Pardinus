package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;

/**
 * An iterator implementing more advanced iteration strategies for temporal
 * solutions.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 *
 * @param <T>
 *            The type to be iterated.
 */
public interface Explorator<T> extends Iterator<T> {

	/**
	 * Produces an alternative solution trace by fixing a set number of states
	 * <code>prefix</code> and enforcing a formula over state <code>prefix</code> +
	 * 1.
	 * 
	 * @param form
	 *            the formula to be enforced at state <code>prefix</code> + 1
	 * @param prefix
	 *            the number of steps to be fixed.
	 */
	public T branch(Formula form, int prefix);
}
