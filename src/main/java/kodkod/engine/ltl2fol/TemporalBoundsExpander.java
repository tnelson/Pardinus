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
public class TemporalBoundsExpander {

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
	static private Universe createUniverse(PardinusBounds oldBounds, int numberOfTimes) {
		List<Object> newAtoms = new ArrayList<Object>();
		Iterator<Object> it = oldBounds.universe().iterator();
		while (it.hasNext()) {
			newAtoms.add(it.next());
		}

		for (int i = 0; i < numberOfTimes; i++) {
			newAtoms.add(TemporalTranslator.STATEATOM + i);
		}

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
			for (int i = 0; i < t.arity(); i++) {
				l.add(t.atom(i));
			}
			tupleSet.add(newUniverse.factory().tuple(l));
		}
		return tupleSet;
	}

	
	/**
	 * Expands the old bounds by converting the bounds over variable relations
	 * into regular bounds with {@link TemporalTranslator#STATE temporal} atoms
	 * appended. It also bounds the constant variables representing the trace.
	 * 
	 * @param bounds
	 *            the bounds with variable relations to be expanded.
	 * @param traceLength
	 *            The number of distinguished states in the trace.
	 * @return
	 */
	public static PardinusBounds expand(PardinusBounds bounds, int traceLength) {
		Universe u = createUniverse(bounds, traceLength);
		return expand(bounds, traceLength, u);
	}

	private static PardinusBounds expand(PardinusBounds bounds, int traceLength, Universe u) {
		PardinusBounds newBounds = new PardinusBounds(u);
		TupleSet tupleSetTime = u.factory().range(
				u.factory().tuple(new Object[] { TemporalTranslator.STATEATOM + "0" }),
				u.factory().tuple(new Object[] { TemporalTranslator.STATEATOM + (traceLength - 1) }));
		bounds.first();
		for (Relation r : bounds.relations()) {
			if (r instanceof VarRelation) {
				TupleSet tupleSetL = convert(bounds.lowerBounds().get(r), u);
				TupleSet tupleSetU = convert(bounds.upperBounds().get(r), u);
				newBounds.bound(((VarRelation) r).expanded, tupleSetL.product(tupleSetTime), tupleSetU.product(tupleSetTime));
			} else {
				TupleSet tupleSetL = convert(bounds.lowerBounds().get(r), u);
				TupleSet tupleSetU = convert(bounds.upperBounds().get(r), u);
				newBounds.bound(r, tupleSetL, tupleSetU);			}
		}

		if (bounds.relationsSymb().size() > 1) 
			throw new UnsupportedOperationException("Expansion of symbolic bounds not yet supported.");

		if (bounds.relationsVars().size() > 1) 
			throw new UnsupportedOperationException("Expansion of trace bounds not yet supported.");

		newBounds.bound(TemporalTranslator.STATE, tupleSetTime);
		newBounds.bound(TemporalTranslator.FIRST, tupleSetTime);
		newBounds.bound(TemporalTranslator.LAST, tupleSetTime);
		newBounds.bound(TemporalTranslator.PREFIX, tupleSetTime.product(tupleSetTime));
		newBounds.bound(TemporalTranslator.LOOP, tupleSetTime.product(tupleSetTime));
		newBounds.bound(TemporalTranslator.TRACE, tupleSetTime.product(tupleSetTime));
		
		if (bounds.amalgamated() != null) {
			PardinusBounds newAmalg = expand(bounds.amalgamated(), traceLength, u);
			newBounds = new PardinusBounds(newBounds,newAmalg);
		}
		
		return newBounds;
	}

}
