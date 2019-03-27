package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.instance.TemporalInstance;

/**
 * An iterator implementing more advanced iteration strategies for temporal
 * solutions.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 *
 * @param <T>
 *            The type to be iterated.
 */
public abstract class Explorator<T> implements Iterator<T> {

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
	public abstract Solution branch(Formula form, int prefix);

	/**
	 * Produces an alternative solution trace by fixing the currently known states
	 * enforcing a formula over the next one.
	 * 
	 * @param form
	 *            the formula to be enforced at state <code>prefix</code> + 1
	 * @param prefix
	 *            the number of steps to be fixed.
	 */
	public Solution extend(Formula form) {
		return branch(form,getLastInstance().states.size()-1);
	}
	
	public abstract TemporalInstance getLastInstance();

}
