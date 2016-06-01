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
import java.util.HashMap;
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
 * @author Eduardo Pessoa, nmm
 *
 */
public class AddTimeToFormula extends AbstractReplacer {

	private Relation next;
	private Relation init;
	
	private int currentPostDepth, maxPostDepth;

	private Formula infinite;

	private Map<String, Relation> relations;

	/**
	 * The relations resulting from the extension of the variable relations.
	 * 
	 * @return
	 */
	Map<String, Relation> getExtendedVarRelations() {
		return relations;
	}

	public AddTimeToFormula(Relation time, Relation next, Relation init, Relation end, Formula infinite) {
		super(new HashSet<Node>());
		this.relations = new HashMap<String, Relation>();
		this.next = next;
		this.init = init;
		this.infinite = infinite;
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
		Formula result = tempFormula.accept(this);
		if (maxPostDepth > 0)
			return forceNextExists(init, maxPostDepth).and(result);
		else
			return result;
	}

	@Override
	public Expression visit(Relation relation) {
		maxPostDepth = currentPostDepth>maxPostDepth?currentPostDepth:maxPostDepth;
		if (isTemporal(relation))
			return getRelation((VarRelation) relation).join(this.getVariable());
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
		int temp = this.currentPostDepth;
		int tempM = this.maxPostDepth;
		resetPostVariables();
		pushOperator(unaryTempFormula.op());
		pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = getQuantifier(getOperator(), e, maxPostDepth);
		popOperator();
		popVariable();
		this.currentPostDepth = temp;
		this.maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		int temp = this.currentPostDepth;
		int tempM = this.maxPostDepth;

		this.pushOperator(binaryTempFormula.op());
		this.pushVariable();
		int quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		Formula rt, left, right;
		switch (binaryTempFormula.op()) {
		case UNTIL:
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.maxPostDepth;
			this.pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = this.maxPostDepth;
			rt = this.getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			this.popVariable();
			break;
		case RELEASE:
			resetPostVariables();
			Formula rightAlways = binaryTempFormula.right().accept(this);
			this.pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = this.maxPostDepth;
			this.pushVariable();
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.maxPostDepth;
			rt = this.getQuantifierRelease(rightAlways, left, right, quantificationPostLeft, quantificationPostRight);
			this.popVariable();
			this.popVariable();
			break;
		default:
			throw new UnsupportedOperationException("Unsupported binary temporal operator:" + binaryTempFormula.op());
		}
		this.popVariable();
		this.popOperator();
		this.currentPostDepth = temp;
		this.maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		this.currentPostDepth++;
		this.pushOperator(TemporalOperator.POST);
		this.pushVariable();
//		// condition to verify the number max of nested plicas!!
//		if (tempExpression.expression() instanceof TempExpression) {
//			numberMaxOfnestedPlicas++;
//		} else {
//			if (numberMaxOfnestedPlicas > this.needToDeclarePostR) {
//				this.needToDeclarePostR = numberMaxOfnestedPlicas;
//				numberMaxOfnestedPlicas = 1;
//			}
//		}
//
//		// if the context is not a temporal operator.
//		if (this.getVariableLastQuantification() == init) {
//			if (numberMaxOfnestedPlicas > this.numberMaxPlicasInit) {
//				this.numberMaxPlicasInit = numberMaxOfnestedPlicas;
//			}
//		}
		Expression localExpression2 = tempExpression.expression().accept(this);
		this.popOperator();
		this.popVariable();
		this.currentPostDepth--;
		return localExpression2;
	}

	private Formula getQuantifierUntil(Formula left, Formula right, int quantificationLeft, int quantificationRight) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Formula nfleft;
		if (quantificationLeft > 0) {
			nfleft = (forceNextExists(l, quantificationLeft).and(left)).forAll(l
					.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(
							next.closure().join(r))));
		} else {
			nfleft = left.forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())
					.intersection(next.closure().join(r))));
		}

		if (quantificationRight > 0) {
			return (forceNextExists(r, quantificationRight).and(right)).and(nfleft).forSome(
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
		Expression quantification = this.getVariableLastQuantification();
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
			v = (Variable) this.getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forSome(
						v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			}
		case NEXT:
		case PREVIOUS:
			Expression v1 = this.getVariable();
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

	// Initialize the original values of the variable needToDeclarePostR and
	// numberMaxOfnestedPlicas
	private void resetPostVariables() {
		currentPostDepth = 0;
		maxPostDepth = 0;
	}

	/* Operators Context */
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();
	private int totalOperators = -1;

	private void pushOperator(TemporalOperator op) {
		this.totalOperators++;
		this.operators.add(op);
	}

	private TemporalOperator getOperator() {
		return this.operators.get(this.totalOperators);
	}

	private boolean thereAreOperator() {
		if (this.operators.size() == 0)
			return false;
		return true;
	}

	private void popOperator() {
		this.operators.remove(this.totalOperators);
		this.totalOperators--;
	}

	/* VarRelations */

	/**
	 * Returns the static relation corresponding to the extension of a variable
	 * relation. Creates it first time.
	 * 
	 * @param name
	 * @param v
	 * @return
	 */
	private Relation getRelation(VarRelation v) {
		Relation e = this.relations.get(v.name());
		if (e == null) {
			Relation varRelation = Relation.nary(v.name(), v.arity() + 1);
			this.relations.put(v.name(), varRelation);
			return varRelation;
		} else {
			return e;
		}
	}

	/* Variables */
	private List<Expression> variables = new ArrayList<Expression>();
	private int totalVar = 0;
	private int totalVariablesIt = 0;

	private void resetVariables() {
		this.variables = new ArrayList<Expression>();
		this.totalVar = 0;
	}

	private void pushVariable() {
		if (!this.thereAreVariables()) {
			this.totalVar++;
			this.variables.add(init);
			return;
		}

		if (this.getOperator() == TemporalOperator.NEXT || this.getOperator() == TemporalOperator.POST) {
			this.variables.add(getVariable().join(next));
		} else {
			if (this.getOperator() == TemporalOperator.PREVIOUS) {
				this.variables.add(getVariable().join(next.transpose()));
			} else {
				Variable v = Variable.unary("t" + this.totalVariablesIt);
				variables.add(v);
				this.totalVariablesIt++;
			}
		}
		this.totalVar++;
	}

	private void popVariable() {
		this.variables.remove(this.totalVar - 1);
		if (this.totalVar > 0)
			this.totalVar--;
	}

	private boolean thereAreVariables() {
		if (this.variables.size() == 0)
			return false;
		return true;
	}

	private Expression getVariable() {
		return this.variables.get(this.totalVar - 1);
	}

	private Expression getVariableLastQuantification() {
		return this.variables.get(this.totalVar - 2);
	}

	private Expression getVariableLastQuantificationUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return this.variables.get(this.totalVar - 3);

		} else {
			return this.variables.get(this.totalVar - 2);

		}
	}

	private Variable getVariableUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return (Variable) this.variables.get(this.totalVar - 1);
		} else {
			return (Variable) this.variables.get(this.totalVar - 2);

		}
	}

	private Expression getVariableLastQuantificationRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return this.variables.get(this.totalVar - 4);
		} else {
			if (!sideIsRight) {
				return this.variables.get(this.totalVar - 3);

			} else {
				return this.variables.get(this.totalVar - 2);

			}
		}
	}

	private Variable getVariableRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return (Variable) this.variables.get(this.totalVar - 3);
		} else {
			if (!sideIsRight) {
				return (Variable) this.variables.get(this.totalVar - 1);

			} else {
				return (Variable) this.variables.get(this.totalVar - 2);

			}
		}
	}

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
