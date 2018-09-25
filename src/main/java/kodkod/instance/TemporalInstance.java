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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.ltl2fol.TemporalTranslator;

/**
 * Represents a temporal instance of a temporal relational problem
 * containing {@link kodkod.ast.VarRelation variable relations} in the
 * {@link kodkod.instance.TemporalBounds temporal bounds}. It is essentially
 * a set of states and a looping state, which is always assumed to exist
 * (i.e., they always represent an infinite path).
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalInstance extends Instance {

	/** The states comprising the trace. */
	public final List<Instance> states;
	/** The looping state. */
	public final int loop;

	/**
	 * Creates a new temporal instance from a sequence of states and a looping
	 * state.
	 * 
	 * @assumes 0 >= loop >= instances.length
	 * @assumes all s,s': instance | s.universe = s'.universe
	 * @param instances
	 *            the states of the temporal instance.
	 * @param loop
	 *            the looping state.
	 * @ensures this.states = instances && this.loop = loop
	 * @throws NullPointerException
	 *             instances = null
	 * @throws IllegalArgumentException
	 *             !(0 >= loop >= instances.length)
	 */
	public TemporalInstance(List<Instance> instances, int loop) {
		super(instances.get(0).universe());
		if (loop < 0 || loop >= instances.size())
			throw new IllegalArgumentException("Looping state must be between 0 and instances.length.");
		this.states = instances;
		this.loop = loop;
	}
	
	/**
	 * Creates a new temporal instance from a static SAT instance that is a solution
	 * to the expansion of the temporal problem. The shape of the trace are
	 * retrieved from the evaluation of the
	 * {@link kodkod.engine.ltl2fol.TemporalTranslator#STATE time} relations. The
	 * original variable relations (prior to expansion) are also considered since
	 * they contain information regarding their temporal properties.
	 * 
	 * NOTE: this should problably be elsewhere and call {@link #TemporalInstance(List, int)}.
	 * 
	 * @assumes some instance.loop
	 * @param instance
	 *            the expanded static solution to the problem
	 * @param tmptrans
	 *            temporal translation information, including original variable
	 *            relations
	 * @throws IllegalArgumentException
	 *             no instance.loop
	 */
	public TemporalInstance(Instance instance, TemporalTranslator tmptrans) {
		super(tmptrans.bounds.universe());
		Evaluator eval = new Evaluator(instance);
		// evaluate last relation
		Tuple tuple_last = eval.evaluate(TemporalTranslator.LAST).iterator().next();
		int end = TemporalTranslator.interpretState(tuple_last);
		// evaluate loop relation
		TupleSet tupleset_loop = eval.evaluate(TemporalTranslator.LOOP);
		if (!tupleset_loop.iterator().hasNext()) 
			throw new IllegalArgumentException("Looping state must exist.");
		Tuple tuple_loop = tupleset_loop.iterator().next();
		loop = TemporalTranslator.interpretState(tuple_loop);

		states = new ArrayList<Instance>();
		// for each state, create a new instance by evaluating relations at that state
		for (int i = 0; i <= end; i++) {
			Instance inst = new Instance(instance.universe());
			
			for (Relation r : tmptrans.bounds.relations()) {
				TupleSet t = eval.evaluate(r,i);
				inst.add(r, t);
			}
			
			states.add(inst);
		}
	}
	
	/**
	 * Converts a temporal instance into a formula that exactly identifies it,
	 * encoding each state of the trace and the looping behavior. Requires that
	 * every relevant atom be reified into a singleton relation, which may be
	 * re-used between calls. Will be used between the various states of the trace.
	 * 
	 * @assumes reif != null
	 * @param reif
	 *            the previously reified atoms
	 * @throws NullPointerException
	 *             reif = null
	 * @return the formula representing <this>
	 */
	// [HASLab]
	public Formula formulate(Map<Object,Relation> reif) {

		// reify atoms not yet reified
		for (int i = 0; i < universe().size(); i++) {
			if (!reif.keySet().contains(universe().atom(i))) {
				Relation r = Relation.unary(universe().atom(i).toString());
				reif.put(universe().atom(i), r);
			}
		}

		// create the constraint for each state
		// S0 and after (S1 and after ...)
		Formula res;
		if (states.isEmpty())
			res = Formula.TRUE;
		else 
			res = states.get(states.size()-1).formulate(reif);
		
		for (int i = states.size()-2; i >= 0; i--)
			res = states.get(i).formulate(reif).and(res.next());

		// create the looping constraint
		// after^loop always (Sloop => after^(end-loop) Sloop && Sloop+1 => after^(end-loop) Sloop+1 && ...)
		Formula rei = states.get(loop).formulate(reif);
		Formula rei2 = rei;
		for (int j = loop; j < states.size(); j++)
			rei2 = rei2.next();

		Formula looping = rei.implies(rei2);
		for (int i = loop+1; i < states.size(); i++) {
			rei = states.get(i).formulate(reif);
			rei2 = rei;
			for (int j = loop; j < states.size(); j++)
				rei2 = rei2.next();
			looping = looping.and(rei.implies(rei2));
		}
		looping = looping.always();
		for (int i = 0; i < loop; i++)
			looping = looping.next();

		res = res.and(looping);
		
		return res;
	}
	
	/**
	 * {@inheritDoc}
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < states.size(); i++) {
			sb.append("* state "+i);
			if (loop == i)
				sb.append(" LOOP");
			if (states.size()-1 == i)
				sb.append(" LAST");
			sb.append("\n"+states.get(i).toString());
			sb.append("\n");
		}
		return sb.toString();
	}

}
