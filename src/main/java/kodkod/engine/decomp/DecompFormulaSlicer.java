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
package kodkod.engine.decomp;

import java.util.AbstractMap.SimpleEntry;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.fol2sat.FormulaFlattener;
import kodkod.engine.fol2sat.RelationCollector;
import kodkod.instance.PardinusBounds;
import kodkod.util.nodes.AnnotatedNode;

/**
 * Slices a first-order logic formula into a pair of conjuncts given a set of
 * variables as the slicing criteria, intended to be used during decomposed
 * model finding. Uses a {@link FormulaFlattener formula flattener} to reduce to
 * NNF and flatten conjuncts, which are then filtered according to the set of
 * variables.
 * 
 * The {@link PardinusBounds bounds} with decomposed information. If the problem
 * is not integrated (still at the first stage), then only set of partial
 * variables occurs in the bounds. If integrated, all variables occur in the
 * bounds, and only those still not constant are considered for the second
 * stage. If the process is at the second stage and every variable is already
 * constant returns the whole formula (probably a case of trivial solution
 * iteration).
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class DecompFormulaSlicer {

	/**
	 * Slices the conjuncts of a formula into two, depending on the variables
	 * selected for the partial problem, as defined in the bounds of the
	 * problem. Considers whether the bounds are already integrated to retrieve
	 * the relevant variables. 
	 *
	 * @param formula
	 *            the formula to be sliced.
	 * @param bounds
	 *            the bounds containing information regarding the selected
	 *            variables.
	 * @return two conjuncts of the formula according to the selected variables.
	 */
	public static Entry<Formula, Formula> slice(Formula formula,
			PardinusBounds bounds) {
		Set<Relation> partials = bounds.relations();
		partials.addAll(bounds.relationsSymb());
		if (bounds.integrated()) {
			Set<Relation> aux = new HashSet<Relation>();
			for (Relation r : partials)
				if (bounds.lowerBound(r).size() == bounds.upperBound(r).size())
					aux.add(r);
			// iterating trivial integrated solutions
			// TODO: there is probably a better way to handle this
			if (partials.equals(aux))
				return new SimpleEntry<Formula, Formula>(Formula.TRUE, formula);
			partials = aux;
		}
		// converts to NNF and flattens the formula
		AnnotatedNode<Formula> flat = FormulaFlattener.flatten(
				AnnotatedNode.annotateRoots(formula), false);
		Formula f1 = flat.node();
		Formula f2 = Formula.TRUE;	
		RelationCollector col = new RelationCollector(flat.sharedNodes());
		// select the appropriate conjuncts
		if (f1 instanceof BinaryFormula
				&& ((BinaryFormula) f1).op() == FormulaOperator.AND) {
			Set<Relation> rsl = ((BinaryFormula) f1).left().accept(col);
			Set<Relation> rsr = ((BinaryFormula) f1).right().accept(col);
			if (partials.containsAll(rsl)) {
				if (!partials.containsAll(rsr)) {
					f2 = ((BinaryFormula) f1).right();
					f1 = ((BinaryFormula) f1).left();
				}
			} else {
				if (partials.containsAll(rsr)) {
					f2 = ((BinaryFormula) f1).left();
					f1 = ((BinaryFormula) f1).right();
				} else {
					f2 = f1;
					f1 = Formula.TRUE;
				}
			}
		} else if (f1 instanceof NaryFormula
				&& ((NaryFormula) f1).op() == FormulaOperator.AND) {
			Iterator<Formula> it = ((NaryFormula) f1).iterator();
			Formula aux = null;
			while (it.hasNext()) {
				Formula f = it.next();
				Set<Relation> rs = f.accept(col);
				if (partials.containsAll(rs))
					aux = aux==null?f:aux.and(f);
				else
					f2 = f2.and(f);
			}
			f1 = aux;
		}
		return new SimpleEntry<Formula, Formula>(f1, f2);
	}
	
	// TODO: temporal slicing will fail if temporal formulas over static relations
}
