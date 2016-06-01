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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.AbstractReplacer;

/**
 * Translates an LTL temporal formula into its standard Kodkod FOL
 * representation.
 * 
 * @author Eduardo Pessoa, nmm
 */
public class LTL2FOLTranslator extends AbstractReplacer {

	/** the relations representing the explicit time trace. */
	private Relation next, init;

	/** the formula forcing the time trace to be infinite. */
	private Formula infinite, structural;

	/**
	 * handle the depth of nested post operators within the current temporal
	 * formula.
	 */
	private int currentPostDepth, maxPostDepth;

	/**
	 * the relations resulting from the extension of the variable relations.
	 * TODO: should this translation be performed here or when the bounds are
	 * converted?
	 */
	private Map<String, Relation> relations;

	/**
	 * Translates an LTL temporal formula into its standard Kodkod FOL
	 * representation.
	 * 
	 * @param timeRels
	 *            the relations representing the time trace, {Time,init,end,next,nextt,loop}.
	 * @param loop
	 *            the relation representing the possible trace loop.
	 */
	public LTL2FOLTranslator(Relation [] timeRels, Map<String,Relation> relations) {
		super(new HashSet<Node>());
		this.relations = relations;
		this.next = timeRels[4];
		this.init = timeRels[1];

		Formula order = timeRels[3].totalOrder(timeRels[0], timeRels[1], timeRels[2]);
		Formula loopDecl = timeRels[5].partialFunction(timeRels[2], timeRels[0]);
		Expression nextDecl = timeRels[3].union(timeRels[5]);
		Formula nextFnct = timeRels[4].eq(nextDecl);
		structural = Formula.and(order, loopDecl, nextFnct);
		infinite = timeRels[5].one();

		resetPostVariables();
		pushVariable();
	}

	/**
	 * Converts a LTL temporal formula into a regular Kodkod FOL formula. Uses
	 * the visitor to convert and adds any trace constraint left at the top
	 * level. This is the main method that should be called to convert temporal
	 * formulas.
	 * 
	 * @param tempFormula
	 *            the LTL formula to be converted.
	 * @return the resulting FOL formula.
	 */
	public Formula convert(Formula tempFormula) {
		Formula result = tempFormula.accept(this).and(structural);
		if (maxPostDepth > 0)
			return forceNextExists(init, maxPostDepth).and(result);
		else
			return result;
	}

	@Override
	public Expression visit(Relation relation) {
		maxPostDepth = currentPostDepth > maxPostDepth ? currentPostDepth : maxPostDepth;
		if (isTemporal(relation))
			return relations.get(relation.name()).join(getVariable());
		else
			return relation;
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (isTemporal(relationPredicate))
			return relationPredicate.toConstraints().accept(this);
		else
			return relationPredicate;
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		int temp = currentPostDepth;
		int tempM = maxPostDepth;
		resetPostVariables();
		pushOperator(unaryTempFormula.op());
		pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = getQuantifier(getOperator(), e, maxPostDepth);
		popOperator();
		popVariable();
		currentPostDepth = temp;
		maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		int temp = currentPostDepth;
		int tempM = maxPostDepth;

		pushOperator(binaryTempFormula.op());
		pushVariable();
		int quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		Formula rt, left, right;
		switch (binaryTempFormula.op()) {
		case UNTIL:
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPostDepth;
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = maxPostDepth;
			rt = getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			popVariable();
			break;
		case RELEASE:
			resetPostVariables();
			Formula rightAlways = binaryTempFormula.right().accept(this);
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = maxPostDepth;
			pushVariable();
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPostDepth;
			rt = getQuantifierRelease(rightAlways, left, right, quantificationPostLeft, quantificationPostRight);
			popVariable();
			popVariable();
			break;
		default:
			throw new UnsupportedOperationException("Unsupported binary temporal operator:" + binaryTempFormula.op());
		}
		popVariable();
		popOperator();
		currentPostDepth = temp;
		maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		currentPostDepth++;
		pushOperator(tempExpression.op());
		pushVariable();
		// // condition to verify the number max of nested plicas!!
		// if (tempExpression.expression() instanceof TempExpression) {
		// numberMaxOfnestedPlicas++;
		// } else {
		// if (numberMaxOfnestedPlicas > needToDeclarePostR) {
		// needToDeclarePostR = numberMaxOfnestedPlicas;
		// numberMaxOfnestedPlicas = 1;
		// }
		// }
		//
		// // if the context is not a temporal operator.
		// if (getVariableLastQuantification() == init) {
		// if (numberMaxOfnestedPlicas > numberMaxPlicasInit) {
		// numberMaxPlicasInit = numberMaxOfnestedPlicas;
		// }
		// }
		Expression localExpression = tempExpression.expression().accept(this);
		popOperator();
		popVariable();
		currentPostDepth--;
		return localExpression;
	}

	private Formula getQuantifierUntil(Formula left, Formula right, int postDepthLeft, int postDepthRight) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Formula nfleft;
		if (postDepthLeft > 0) {
			nfleft = (forceNextExists(l, postDepthLeft).and(left)).forAll(l
					.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(
							next.closure().join(r))));
		} else {
			nfleft = left.forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())
					.intersection(next.closure().join(r))));
		}

		if (postDepthRight > 0) {
			return (forceNextExists(r, postDepthRight).and(right)).and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		} else {
			return right.and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		}
	}

	private Formula getQuantifierRelease(Formula always, Formula left, Formula right, int leftFormula, int rightFormula) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;

		alw = infinite.and(always.forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(
				next.reflexiveClosure()))));

		if (rightFormula > 0) {
			nfleft = (forceNextExists(l, rightFormula).and(right)).forAll(l.oneOf(getVariableLastQuantificationRelease(
					false, true).join(next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		} else {
			nfleft = right.forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(
					next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		}

		if (leftFormula > 0) {
			nfright = (forceNextExists(r, leftFormula).and(left)).and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure())));
		} else {
			nfright = left.and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure())));
		}
		return alw.or(nfright);
	}

	private Formula getQuantifier(TemporalOperator op, Formula e, int posts) {
		Variable v;
		Expression quantification = getVariableLastQuantification();
		switch (op) {
		case ALWAYS:
			v = (Variable) getVariable();
			return infinite.and(e.forAll(v.oneOf(quantification.join(next.reflexiveClosure()))));
		case EVENTUALLY:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forSome(v.oneOf(quantification.join(next.reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(next.reflexiveClosure())));
			}
		case HISTORICALLY:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forAll(
						v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			} else {
				return e.forAll(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			}
		case ONCE:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forSome(
						v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			}
		case NEXT:
		case PREVIOUS:
			Expression v1 = getVariable();
			if (posts > 0) {
				return forceNextExists(v1, posts).and(v1.some().and(e));
			} else {
				return v1.some().and(e);
			}
		default:
			return e;
		}
	}

	private Formula forceNextExists(Expression exp, int x) {
		Expression e = exp.join(next);
		for (int i = 1; i < x; i++) {
			e = e.join(next);
		}
		return e.some();
	}

	/**
	 * Resets the original values of the variable nested post operators
	 * accumulators. Should be called whenever a new temporal variable is
	 * quantified.
	 */
	private void resetPostVariables() {
		currentPostDepth = 0;
		maxPostDepth = 0;
	}

	/* Operators Context */
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();

	private void pushOperator(TemporalOperator op) {
		operators.add(op);
	}

	private TemporalOperator getOperator() {
		return operators.get(operators.size() - 1);
	}

	// private boolean thereAreOperator() {
	// if (operators.size() == 0)
	// return false;
	// return true;
	// }

	private void popOperator() {
		operators.remove(operators.size() - 1);
	}

	/* Variables */
	private List<Expression> variables = new ArrayList<Expression>();
	private int totalVariablesIt = 0;

	// private void resetVariables() {
	// variables = new ArrayList<Expression>();
	// totalVar = 0;
	// }

	private void pushVariable() {
		if (!thereAreVariables()) {
			variables.add(init);
			return;
		}

		switch (getOperator()) {
		case NEXT:
		case POST:
			variables.add(getVariable().join(next));
			break;
		case PREVIOUS:
			variables.add(getVariable().join(next.transpose()));
			break;
		default:
			Variable v = Variable.unary("t" + totalVariablesIt);
			variables.add(v);
			totalVariablesIt++;
		}
	}

	private void popVariable() {
		variables.remove(variables.size() - 1);
	}

	private boolean thereAreVariables() {
		return !variables.isEmpty();
		// if (variables.size() == 0)
		// return false;
		// return true;
	}

	private Expression getVariable() {
		return variables.get(variables.size() - 1);
	}

	private Expression getVariableLastQuantification() {
		return variables.get(variables.size() - 2);
	}

	private Expression getVariableLastQuantificationUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return variables.get(variables.size() - 3);
		} else {
			return variables.get(variables.size() - 2);
		}
	}

	private Variable getVariableUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return (Variable) variables.get(variables.size() - 1);
		} else {
			return (Variable) variables.get(variables.size() - 2);
		}
	}

	private Expression getVariableLastQuantificationRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return variables.get(variables.size() - 4);
		} else {
			if (!sideIsRight) {
				return variables.get(variables.size() - 3);
			} else {
				return variables.get(variables.size() - 2);
			}
		}
	}

	private Variable getVariableRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return (Variable) variables.get(variables.size() - 3);
		} else {
			if (!sideIsRight) {
				return (Variable) variables.get(variables.size() - 1);
			} else {
				return (Variable) variables.get(variables.size() - 2);
			}
		}
	}

	/**
	 * Checks whether an AST node has temporal constructs.
	 * 
	 * @param n
	 *            the node to be checked.
	 * @return whether n has temporal constructs.
	 */
	private final boolean isTemporal(Node n) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}

			public Boolean visit(Relation relation) {
				return cache(relation, relation instanceof VarRelation);
			}
		};
		return (boolean) n.accept(det);
	}

}
