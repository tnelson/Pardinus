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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.engine.ltl2fol.TemporalTranslator;

/**
 * Represents a temporal model (an instance) of a temporal relational problem
 * containing {@link kodkod.ast.VarRelation variable relations} in the
 * {@link kodkod.instance.TemporalBounds temporal bounds}. Although the instance
 * is a solution to the expansion of the temporal problem into a regular static
 * Kodkod problem, it should be interpreted as a trace, i.e., a mapping from
 * states instances. The methods inherited from regular
 * {@link kodkod.instance.Instance instances} act upon the expanded instance.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalInstance extends Instance {

	/**
	 * Variables representing the shape of the trace of the solution.
	 */
	public final int loop;

	public final List<Instance> states;

	/**
	 * Creates a new temporal instance from a static instance that is a solution
	 * to the expansion of the temporal problem. The shape of the trace are
	 * retrieved from the evaluation of the
	 * {@link kodkod.engine.ltl2fol.TemporalTranslator#STATE time} relations. The
	 * original variable relations are also considered since they contain
	 * information regarding their expansion into the static problem.
	 * 
	 * @param instance
	 *            the expanded static solution to the problem
	 * @param tmptrans 
	 * @param varrelations
	 *            the original variable relations
	 */
	public TemporalInstance(Instance instance, TemporalTranslator tmptrans) {
		super(tmptrans.bounds.universe(), new LinkedHashMap<Relation, TupleSet>(instance.relationTuples()), instance.intTuples());
		Evaluator eval = new Evaluator(instance);
		Tuple tuple_last = eval.evaluate(TemporalTranslator.LAST).iterator().next();
		int end = TemporalTranslator.interpretState(tuple_last);
		TupleSet tupleset_loop = eval.evaluate(TemporalTranslator.LOOP);
		if (tupleset_loop.iterator().hasNext()) {
			Tuple tuple_loop = tupleset_loop.iterator().next();
			loop = TemporalTranslator.interpretState(tuple_loop);
		}
		else 
			loop = -1;
		
		states = new ArrayList<Instance>();
		for (int i = 0; i <= end; i++) {
			Instance inst = new Instance(instance.universe());
			
			for (Relation r : tmptrans.bounds.relations()) {
				TupleSet t = eval.evaluate(r,i);
				inst.add(r, t);
			}
			
			states.add(inst);
		}
	}

	public TemporalInstance(List<Instance> instances, int loop) {
		super(instances.get(0).universe());
		this.states = instances;
		this.loop = loop;
	}
	
	// [HASLab]
	public Formula reify(Map<Object,Relation> reif) {

		if (reif.isEmpty())
			for (int i = 0; i < universe().size(); i++) {
				Relation r = Relation.unary(universe().atom(i).toString());
				reif.put(universe().atom(i), r);
			}
		
		Formula res = Formula.TRUE;

		for (int i = states.size()-1; i >= 0; i--)
			res = states.get(i).reify(reif).and(res.next());

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
			sb.append(states.get(i).toString());
			sb.append("\n");
		}
		sb.append("loop: ");
		sb.append(loop);
		return sb.toString();
	}

}
