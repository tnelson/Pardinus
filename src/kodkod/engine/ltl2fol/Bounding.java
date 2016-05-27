/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
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

import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.instance.*;

import java.util.*;

/**
 * This class creates new bounds with based on the old bounds(without temporal
 * references). The temporal relations' bounds are filed with the Time atoms
 * created in this class based on the number of times defined by the user.
 *
 * @author Eduardo Pessoa, nmm
 *
 */
public class Bounding {
	private Bounds oldBounds;

	private int numberOfTimes;

	private Universe universe;
	private TupleFactory tupleFactory;
	private Bounds bounds;
	private Relation[] timedRelations;
	private Map<String, Relation> extendedVarRelations;

	public Bounding(Bounds oldBounds, int numberOfTimes, Relation[] time, Map<String, Relation> extendedVarRelations,
			Set<Relation> dynamicRelations) {
		this.oldBounds = oldBounds;
		this.numberOfTimes = numberOfTimes;
		this.timedRelations = time;
		this.extendedVarRelations = extendedVarRelations;
		this.createUniverse();
		this.bounding();
	}

	public Bounds getExpandedBounds() {
		return bounds;
	}

	/**
	 * Expands the old bounds by converting the variable bounds into regular
	 * bounds with a Time atom appended.
	 */
	private void bounding() {
		TupleSet tupleSetTime = this.tupleFactory.range(this.tupleFactory.tuple(new Object[] { "Time0" }),
				this.tupleFactory.tuple(new Object[] { "Time" + (this.numberOfTimes - 1) }));
		for (Relation r : this.oldBounds.relations()) {
			if (r instanceof VarRelation) {
				this.makeNewTuplesFromOldBounds(r, tupleSetTime);
			} else {
				this.makeNewTuplesFromOldBounds(r);
			}
		}

		bounds.bound(timedRelations[0], tupleSetTime);// Time
		bounds.bound(timedRelations[1], tupleSetTime);// init
		bounds.bound(timedRelations[2], tupleSetTime);// end
		bounds.bound(timedRelations[3], tupleSetTime.product(tupleSetTime));// next
		bounds.bound(timedRelations[4], tupleSetTime.product(tupleSetTime));// loop
		bounds.bound(timedRelations[5], tupleSetTime.product(tupleSetTime));// nextt
	}

	/*-------------------------*/

	/**
	 * Create a new universe by adding numberOfTimes Time atoms.
	 */
	private void createUniverse() {
		ArrayList<Object> localArrayList = new ArrayList<Object>();
		Iterator<Object> it = this.oldBounds.universe().iterator();
		while (it.hasNext()) {
			localArrayList.add(it.next());
		}

		for (int i = 0; i < this.numberOfTimes; i++) {
			localArrayList.add("Time" + i);
		}

		this.universe = new Universe(localArrayList);
		this.tupleFactory = this.universe.factory();
		this.bounds = new Bounds(this.universe);
	}

	/**
	 * Converts the existing bounds of a variable relation into ones with the
	 * current universe, appending the Time atoms.
	 * 
	 * @param relation
	 *            the variable relation whose bounds are to be converted
	 * @param tupleSetTime
	 *            the time atoms in the universe
	 */
	private void makeNewTuplesFromOldBounds(Relation relation, TupleSet tupleSetTime) {
		TupleSet tupleSetL = convert(oldBounds.lowerBounds().get(relation));
		TupleSet tupleSetU = convert(oldBounds.upperBounds().get(relation));

		bounds.bound(this.extendedVarRelations.get(relation.name()), tupleSetL.product(tupleSetTime),
				tupleSetU.product(tupleSetTime));
	}

	/**
	 * Converts the existing bounds of a static relation into ones with the
	 * current universe.
	 * 
	 * @param relation
	 *            the static relation whose bounds are to be converted
	 */
	private void makeNewTuplesFromOldBounds(Relation relation) {
		TupleSet tupleSetL = convert(oldBounds.lowerBounds().get(relation));
		TupleSet tupleSetU = convert(oldBounds.upperBounds().get(relation));

		bounds.bound(relation, tupleSetL, tupleSetU);
	}

	/**
	 * Converts an existing tuple set into an identical tuple set with the
	 * current universe.
	 * 
	 * @param ts
	 *            the existing tuple set
	 * @return the converted tuple set
	 */
	private TupleSet convert(TupleSet ts) {
		TupleSet tupleSet = this.tupleFactory.noneOf(ts.arity());
		Iterator<Tuple> itr = ts.iterator();
		while (itr.hasNext()) {
			Tuple t = itr.next();
			List<Object> l = new ArrayList<Object>();
			for (int i = 0; i < t.arity(); i++) {
				l.add(t.atom(i));
			}
			tupleSet.add(this.tupleFactory.tuple(l));
		}
		return tupleSet;
	}

}
