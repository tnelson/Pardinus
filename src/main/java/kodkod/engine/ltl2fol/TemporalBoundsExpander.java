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
package kodkod.engine.ltl2fol;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * An extension to the regular Kodkod {@link Bounds bounds} that stores
 * information regarding its origin from bounds over {@link VarRelation variable
 * relations}. Translates {@link VarRelation variable relation} bounds into its
 * standard representation, by appending the {@link TemporalTranslator#STATE time
 * sig} to the bound. The bounds of static relations should remain unchanged.
 * The temporal options will define the maximum size of the trace. It will also
 * store the mapping of the variable relations into their expanded versions
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
class TemporalBoundsExpander {

	/**
	 * Create a new universe by duplicating the original one and creating a
	 * given number of {@link TemporalTranlator#STATE time} atoms.
	 *
	 * @param oldBounds
	 *            the original bounds.
	 * @param numberOfTimes
	 *            the number of time atoms.
	 * @return a new universe with the atoms of the original one plus the time
	 *         ones.
	 */
	static private Universe createUniverse(PardinusBounds oldBounds, int numberOfTimes, int numberOfUnrolls) {
		List<Object> newAtoms = new ArrayList<Object>();
		Iterator<Object> it = oldBounds.universe().iterator();
		while (it.hasNext())
			newAtoms.add(it.next());

//		for (int i = 0; i < numberOfTimes; i++)
//			newAtoms.add(TemporalTranslator.STATEATOM + i);

		for (int j = 0; j < numberOfUnrolls; j++)
			for (int i = 0; i < numberOfTimes; i++)
				newAtoms.add(TemporalTranslator.STATEATOM_UNR + i + "_" + j);

		return new Universe(newAtoms);
	}

	/**
	 * Converts an existing tuple set into an identical tuple set with the
	 * current universe.
	 * 
	 * @param ts
	 *            the existing tuple set
	 * @return the converted tuple set
	 */
	static private TupleSet convert(TupleSet ts, Universe newUniverse) {
		TupleSet tupleSet = newUniverse.factory().noneOf(ts.arity());
		Iterator<Tuple> itr = ts.iterator();
		while (itr.hasNext()) {
			Tuple t = itr.next();
			List<Object> l = new ArrayList<Object>();
			for (int i = 0; i < t.arity(); i++)
				l.add(t.atom(i));
			tupleSet.add(newUniverse.factory().tuple(l));
		}
		return tupleSet;
	}

	
	/**
	 * Expands the old bounds by converting the bounds over variable relations
	 * into regular bounds with {@link TemporalTranslator#STATE temporal} atoms
	 * appended. It also binds the constant variables representing the trace.
	 * 
	 * @param bounds
	 *            the bounds with variable relations to be expanded.
	 * @param traceLen
	 *            the number of distinguished states in the trace.
	 * @return the expanded bounds
	 */
	static PardinusBounds expand(PardinusBounds bounds, int traceLen, int unrolls) {
		Universe u = createUniverse(bounds, traceLen, unrolls);
		return expand(bounds, traceLen, u, unrolls);
	}

	/**
	 * Actually expands temporal bounds into their static representation as regular
	 * bounds with {@link TemporalTranslator#STATE temporal} atoms appended.
	 * 
	 * Bounds are assumed to already be expanded at this point. Also, trace bounds
	 * with more than a state are not yet implemented.
	 * 
	 * TODO support trace bounds with multiple steps.
	 * 
	 * @param bounds
	 *            the original temporal bounds
	 * @param traceLen
	 *            the number of distinguished states in the trace.
	 * @param u
	 *            the new universe
	 * @return the expanded bounds with the new universe
	 */
	private static PardinusBounds expand(PardinusBounds bounds, int traceLen, Universe u, int unr) {
		if (bounds.boundTrace().size() > 1) 
			throw new UnsupportedOperationException("Expansion of trace bounds not yet supported.");

		for (Relation r : bounds.relationsSymb())
			if (bounds.upperBound(r) == null)
				throw new UnsupportedOperationException("Expansion of symbolic bounds not yet supported.");

		PardinusBounds newBounds = new PardinusBounds(u);
//		TupleSet tupleSetTime = u.factory().range(
//				u.factory().tuple(TemporalTranslator.STATEATOM + "0"),
//				u.factory().tuple(TemporalTranslator.STATEATOM + (traceLen - 1)));
		TupleSet tupleSetTime_unr_last = u.factory().range(
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + "0"+"_"+(unr - 1)),
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen - 1)+"_"+(unr - 1)));
				
//		TupleSet last = u.factory().setOf(u.factory().tuple(TemporalTranslator.STATEATOM + (traceLen - 1)));
//		TupleSet trace = u.factory().noneOf(2);
//		for (int i = 0; i < traceLen-1; i++)
//			trace.add(u.factory().tuple(TemporalTranslator.STATEATOM + i,TemporalTranslator.STATEATOM + (i+1)));
			
//		newBounds.boundExactly(TemporalTranslator.STATE, tupleSetTime);
//		newBounds.boundExactly(TemporalTranslator.FIRST, u.factory().setOf(u.factory().tuple(TemporalTranslator.STATEATOM + "0")));
//		newBounds.boundExactly(TemporalTranslator.LAST, last);
//		newBounds.boundExactly(TemporalTranslator.PREFIX, trace);
//		newBounds.bound(TemporalTranslator.LOOP, tupleSetTime);
		
		TupleSet tupleSetTime_unr = u.factory().range(
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + "0_0"),
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen - 1) +"_"+(unr - 1)));
		
		TupleSet tupleSetTime_unr_first = u.factory().range(
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + "0_0"),
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen - 1)+"_"+"0"));
		
		TupleSet tupleSetTime_unr_first_lasts = u.factory().range(
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + "0_0"),
				u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen - 1)+"_"+"0"));
		for (int j = 0; j < unr; j++)
			tupleSetTime_unr_first_lasts.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen-1)+"_"+j));

		newBounds.bound(TemporalTranslator.STATE_UNR, tupleSetTime_unr_first_lasts, tupleSetTime_unr); 
		
		newBounds.boundExactly(TemporalTranslator.FIRST_UNR, u.factory().setOf(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + "0_0")));

		TupleSet last_unr = u.factory().setOf(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen - 1)+"_"+(unr - 1)));
		newBounds.boundExactly(TemporalTranslator.LAST_UNR, last_unr);
		newBounds.bound(TemporalTranslator.LOOP_UNR, tupleSetTime_unr_last);

		TupleSet trace_unr = u.factory().noneOf(2);
		TupleSet trace_unr_l = u.factory().noneOf(2);
		for (int i = 0; i < traceLen-1; i++) {
			trace_unr.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + i+"_"+0,TemporalTranslator.STATEATOM_UNR + (i+1)+"_"+0));
			trace_unr_l.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + i+"_"+0,TemporalTranslator.STATEATOM_UNR + (i+1)+"_"+0));
		}
		if (1 < unr)
			for (int k = 0; k < traceLen; k++) 
				trace_unr.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen-1)+"_"+0,TemporalTranslator.STATEATOM_UNR + k+"_"+1));
		for (int j = 1; j < unr; j++) {
			for (int i = 0; i < traceLen-1; i++) 
				for (int k = i+1; k < traceLen; k++) 
					trace_unr.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + i+"_"+j,TemporalTranslator.STATEATOM_UNR + k+"_"+j));
			if (j < unr - 1)
				for (int k = 0; k < traceLen; k++) 
					trace_unr.add(u.factory().tuple(TemporalTranslator.STATEATOM_UNR + (traceLen-1)+"_"+j,TemporalTranslator.STATEATOM_UNR + k+"_"+(j+1)));
		}
		
		newBounds.bound(TemporalTranslator.PREFIX_UNR, trace_unr_l, trace_unr); 

		TupleSet unrollMap = u.factory().noneOf(2);
		TupleSet unrollMap_l = u.factory().noneOf(2);
		for (int i = 0; i < traceLen; i++) {
			unrollMap_l.add(u.factory().tuple(new Object[] { TemporalTranslator.STATEATOM_UNR + i + "_" + 0, TemporalTranslator.STATEATOM_UNR + i + "_" + 0 }));
			unrollMap.add(u.factory().tuple(new Object[] { TemporalTranslator.STATEATOM_UNR + i + "_" + 0, TemporalTranslator.STATEATOM_UNR + i + "_" + 0 }));
		}
		for (int i = 0; i < traceLen; i++)
			for (int j = 1; j < unr; j++) 
				unrollMap.add(u.factory().tuple(new Object[] { TemporalTranslator.STATEATOM_UNR + i + "_" + j, TemporalTranslator.STATEATOM_UNR + i + "_" + 0 }));

		newBounds.bound(TemporalTranslator.UNROLL_MAP, unrollMap_l, unrollMap);

		bounds.first();
		for (Relation r : bounds.relations()) {
			TupleSet tupleSetL = convert(bounds.lowerBound(r), u);
			TupleSet tupleSetU = convert(bounds.upperBound(r), u);
			if (r instanceof VarRelation) {
				newBounds.bound(((VarRelation) r).expanded, tupleSetL.product(tupleSetTime_unr_first), tupleSetU.product(tupleSetTime_unr_first));
				if (bounds.target(r) != null) {
					TupleSet tupleSetT = convert(bounds.target(r), u);
					newBounds.setTarget(((VarRelation) r).expanded, tupleSetT.product(tupleSetTime_unr_first));
				}
				if (bounds.weight(r) != null) 
					newBounds.setWeight(((VarRelation) r).expanded, bounds.weight(r));
			} else {
				newBounds.bound(r, tupleSetL, tupleSetU);			
				if (bounds.target(r) != null) {
					TupleSet tupleSetT = convert(bounds.target(r), u);
					newBounds.setTarget(r, tupleSetT);
				}
				if (bounds.weight(r) != null) 
					newBounds.setWeight(r, bounds.weight(r));
			}
		}

		
		newBounds.amalgamated = bounds.amalgamated;
		newBounds.trivial_config = bounds.trivial_config;
		newBounds.integrated = bounds.integrated;
		newBounds.integration = bounds.integration;
		
		if (bounds.amalgamated() != null) {
			PardinusBounds newAmalg = expand(bounds.amalgamated(), traceLen, u, unr);
			newBounds = new PardinusBounds(newBounds,newAmalg);
		}
		
		return newBounds;
	}

}
