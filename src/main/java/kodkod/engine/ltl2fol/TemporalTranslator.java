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

import java.util.HashSet;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.VarRelation;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;

/**
 * Translates temporal problems, i.e., formulas with
 * {@link kodkod.ast.operator.TemporalOperator temporal operators} and bounds
 * over {@link kodkod.ast.VarRelation variable relations}, into regular Kodkod
 * static problems, i.e., standard {@link kodkod.ast.Formula formulas} and
 * {@link kodkod.instance.Bounds bounds}, following the provided
 * {@link kodkod.engine.config.TemporalOptions temporal options}.
 *
 * Relations are introduced to explicitly model the (bounded) temporal trace,
 * and variable relations are expanded to static ones that refer to that trace.
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalTranslator {

	/** The name assigned to {@link #STATE state} atoms. */
	public static final String STATEATOM = "Time";
	public static final String STATEATOM_UNR = "TimeUnr";

	/** Relations representing the explicit trace of the temporal problem. **/
	public static final Relation STATE = Relation.unary(STATEATOM);
	public static final Relation FIRST = Relation.unary("first");
	public static final Relation LAST = Relation.unary("last");
	public static final Relation PREFIX = Relation.binary("prefix");
	public static final Relation TRACE = Relation.binary("trace");
	public static final Relation LOOP = Relation.binary("loop");

	public static final Relation STATE_UNR = Relation.unary(STATEATOM_UNR);
	public static final Relation FIRST_UNR = Relation.unary("first_unr");
	public static final Relation LAST_UNR = Relation.unary("last_unr");
	public static final Relation PREFIX_UNR = Relation.binary("prefix_unr");
	public static final Relation TRACE_UNR = Relation.binary("trace_unr");
	public static final Relation LOOP_UNR = Relation.binary("loop_unr");

	/**
	 * The constraint forcing the time trace to be infinite. Forces the loop to
	 * exist.
	 */
	public static final Formula INFINITE = TemporalTranslator.LOOP.one();

	/**
	 * Translates {@link kodkod.instance.TemporalBounds temporal bound} into
	 * standard bounds by expanding the bound trace over
	 * {@link kodkod.ast.VarRelation variable relations} by appending the
	 * {@link #STATE state sig} to the bound. The bounds of static relations
	 * should remain unchanged. The temporal options will define the maximum
	 * size of the trace.
	 * 
	 * @see TemporalBoundsExpander
	 * 
	 * @param bounds
	 *            the temporal bounds to be expanded.
	 * @param traceLength
	 *            the trace length.
	 * @return the temporal bounds expanded into standard bounds.
	 */
	public static Bounds translate(PardinusBounds bounds, int traceLength) {
		return TemporalBoundsExpander.expand(bounds, traceLength);
	}

	/**
	 * Converts an LTL temporal formula into its FOL static representation,
	 * provided the temporal options. The formula is previously converted into
	 * negative normal form (NNF) to guarantee the correct translation of the
	 * temporal operators. The {@link kodkod.ast.VarRelation variable relations}
	 * contain themselves their representation into the expanded static shape.
	 * 
	 * @see LTL2FOLTranslator
	 * 
	 * @param formula
	 *            the temporal formula to be expanded.
	 * @return the static version of the temporal formula.
	 */
	public static Formula translate(Formula formula) {
		Formula nnfFormula = NNFReplacer.nnf(formula);
		return LTL2FOLTranslator.translate(nnfFormula);
	}

	/**
	 * Checks whether an AST node has temporal constructs, i.e., occurrences of
	 * {@link kodkod.ast.operator.TemporalOperator temporal operations} or
	 * {@link kodkod.ast.VarRelation variable relations}.
	 * 
	 * @param node
	 *            the node to be checked.
	 * @return whether the node has temporal constructs.
	 */
	public static boolean isTemporal(Node node) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			@Override
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}

			@Override
			public Boolean visit(Relation relation) {
				return cache(relation, relation instanceof VarRelation);
			}
		};
		return (boolean) node.accept(det);
	}

}
