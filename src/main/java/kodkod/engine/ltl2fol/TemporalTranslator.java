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
import java.util.Iterator;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NaryIntExpression;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.RelationPredicate.Function;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.ReturnVisitor;
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
//	public static final String STATEATOM = "Time";
	public static final String STATEATOM_UNR = "TimeUnr";

	/** Relations representing the explicit trace of the temporal problem. **/
//	public static final Relation STATE = Relation.unary(STATEATOM);
//	public static final Relation FIRST = Relation.unary("first");
//	public static final Relation LAST = Relation.unary("last");
//	public static final Relation PREFIX = Relation.binary("prefix");
//	public static final Relation LOOP = Relation.unary("loop");
//	public static final Expression TRACE = PREFIX.union(LAST.product(LOOP));

	public static final Relation STATE_UNR = Relation.unary(STATEATOM_UNR);
	public static final Relation FIRST_UNR = Relation.unary("first_unr");
	public static final Relation LAST_UNR = Relation.unary("last_unr");
	public static final Relation PREFIX_UNR = Relation.binary("prefix_unr");
	public static final Relation LOOP_UNR = Relation.unary("loop_unr");
	public static final Expression TRACE_UNR = PREFIX_UNR.union(LAST_UNR.product(LOOP_UNR));

	public static final Relation UNROLL_MAP = Relation.binary("unroll_map");
	
	/**
	 * The constraint forcing the time trace to be infinite. Forces the loop to
	 * exist.
	 */
	public static final Formula INFINITE = TemporalTranslator.LOOP_UNR.one();

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
	public static Bounds translate(PardinusBounds bounds, int traceLength, int unrolls) {
		return TemporalBoundsExpander.expand(bounds, traceLength, unrolls);
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
	public static Formula translate(Formula formula, int n) {
		Formula nnfFormula = NNFReplacer.nnf(formula);
		return LTL2FOLTranslator.translate(nnfFormula, n);
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
	
	/** Count the height of the given Kodkod AST tree. */
	public static int countHeight(Node node) {
		ReturnVisitor<Integer,Integer,Integer,Integer> vis = new ReturnVisitor<Integer,Integer,Integer,Integer>() {
			private int max(int a, int b)                 { return (a>=b) ? a : b; }
			private int max(int a, int b, int c)          { return (a>=b) ? (a>=c ? a : c) : (b>=c ? b: c); }
			public Integer visit(Relation x)              { return 0; }
			public Integer visit(IntConstant x)           { return 0; }
			public Integer visit(ConstantFormula x)       { return 0; }
			public Integer visit(Variable x)              { return 0; }
			public Integer visit(ConstantExpression x)    { return 0; }
			public Integer visit(NotFormula x)            { return x.formula().accept(this); }
			public Integer visit(UnaryTempFormula x)      { 
				int n = 0;
				if (x.op().equals(TemporalOperator.ONCE)||x.op().equals(TemporalOperator.HISTORICALLY)||x.op().equals(TemporalOperator.PREVIOUS)) 
					n = 1;
				int l = x.formula().accept(this);
				return n + l; } // [HASLab] temporal nodes
			public Integer visit(IntToExprCast x)         { return x.intExpr().accept(this); }
			public Integer visit(Decl x)                  { return x.expression().accept(this); }
			public Integer visit(ExprToIntCast x)         { return x.expression().accept(this); }
			public Integer visit(UnaryExpression x)       { return x.expression().accept(this); }
			public Integer visit(TempExpression x)        { return x.expression().accept(this); } // [HASLab] temporal nodes
			public Integer visit(UnaryIntExpression x)    { return x.intExpr().accept(this); }
			public Integer visit(MultiplicityFormula x)   { return x.expression().accept(this); }
			public Integer visit(BinaryExpression x)      { return max(x.left().accept(this), x.right().accept(this)); }
			public Integer visit(ComparisonFormula x)     { return max(x.left().accept(this), x.right().accept(this)); }
			public Integer visit(BinaryFormula x)         { return max(x.left().accept(this), x.right().accept(this)); }
			public Integer visit(BinaryTempFormula x)     { 
				int n = 0;
				if (x.op().equals(TemporalOperator.SINCE)||x.op().equals(TemporalOperator.TRIGGER)) 
					n = 1;
				int l = max(x.left().accept(this), x.right().accept(this));
				return n + l; } // [HASLab] temporal nodes
			public Integer visit(BinaryIntExpression x)   { return max(x.left().accept(this), x.right().accept(this)); }
			public Integer visit(IntComparisonFormula x)  { return max(x.left().accept(this), x.right().accept(this)); }
			public Integer visit(IfExpression x)          { return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this)); }
			public Integer visit(IfIntExpression x)       { return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this)); }
			public Integer visit(SumExpression x)         { return max(x.decls().accept(this), x.intExpr().accept(this)); }
			public Integer visit(QuantifiedFormula x)     { return max(x.decls().accept(this), x.formula().accept(this)); }
			public Integer visit(Comprehension x)         { return max(x.decls().accept(this), x.formula().accept(this)); }
			public Integer visit(Decls x) {
				int max = 0, n = x.size();
				for(int i=0; i<n; i++) max = max(max, x.get(i).accept(this));
				return max;
			}
			public Integer visit(ProjectExpression x) {
				int max = x.expression().accept(this);
				for(Iterator<IntExpression> t = x.columns(); t.hasNext();) { max = max(max, t.next().accept(this)); }
				return max;
			}
			public Integer visit(RelationPredicate x) {
				if (x instanceof Function) {
					Function f = ((Function)x);
					return max(f.domain().accept(this), f.range().accept(this));
				}
				return 0;
			}
			public Integer visit(NaryExpression x) {
				int max = 0;
				for(int m=0, n=x.size(), i=0; i<n; i++) { m=x.child(i).accept(this); if (i==0 || max<m) max=m; }
				return max;
			}
			public Integer visit(NaryIntExpression x) {
				int max = 0;
				for(int m=0, n=x.size(), i=0; i<n; i++) { m=x.child(i).accept(this); if (i==0 || max<m) max=m; }
				return max;
			}
			public Integer visit(NaryFormula x) {
				int max = 0;
				for(int m=0, n=x.size(), i=0; i<n; i++) {
					m=x.child(i).accept(this); 
					if (i==0 || max<m) 
						max=m; 
					}
				return max;
			}
		};
		Object ans = node.accept(vis);
		if (ans instanceof Integer) return ((Integer)ans).intValue()+1; else return 1;
	}


}
