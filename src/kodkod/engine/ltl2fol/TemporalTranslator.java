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
import kodkod.instance.TemporalBounds;

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
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
public class TemporalTranslator {

	/** The name assigned to {@link #STATE state} atoms. */
	public static String STATEATOM = "Time";

	/** Relations representing the explicit trace of the temporal problem. **/
	public static Relation STATE = Relation.unary(STATEATOM);
	public static Relation FIRST = Relation.unary("first");
	public static Relation LAST = Relation.unary("last");
	public static Relation PREFIX = Relation.binary("prefix");
	public static Relation TRACE = Relation.binary("trace");
	public static Relation LOOP = Relation.binary("loop");

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
	public static Bounds translate(TemporalBounds bounds, int traceLength) {
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
		NNFReplacer nnf = new NNFReplacer();
		Formula nnfFormula = formula.accept(nnf);

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
