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
import java.util.HashSet;
import java.util.List;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ConstantExpression;
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
import kodkod.ast.visitor.AbstractReplacer;
import static kodkod.engine.ltl2fol.TemporalTranslator.INFINITE;
import static kodkod.engine.ltl2fol.TemporalTranslator.FIRST;
import static kodkod.engine.ltl2fol.TemporalTranslator.LAST;
import static kodkod.engine.ltl2fol.TemporalTranslator.LOOP;
import static kodkod.engine.ltl2fol.TemporalTranslator.PREFIX;
import static kodkod.engine.ltl2fol.TemporalTranslator.STATE;
import static kodkod.engine.ltl2fol.TemporalTranslator.TRACE;
import static kodkod.engine.ltl2fol.TemporalTranslator.UNROLL_MAP;

/**
 * Translates an LTL temporal formula into its standard Kodkod FOL
 * representation. Assumes that the variable relations have been previously
 * expanded into its static version. To do so, it explicitly introduces the time
 * elements into the formula, converting the temporal operators into time
 * quantifiers and applying the time variable to variable relations. Since
 * global temporal quantifications force the trace to be infinite, the formula
 * must be in negative normal form to guarantee a correct translation.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class LTL2FOLTranslator extends AbstractReplacer {

	/**
	 * Variables to handle the depth of nested post operators within the current
	 * temporal formula.
	 */
	private int curPrimeDepth, maxPrimeDepth;

	/** Pre-computed information about the formula, allows optimizations. */
	private boolean has_always, has_past;

	/**
	 * Translates an LTL temporal formula into its standard Kodkod FOL
	 * representation, given the extension of the variable relations.
	 * 
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 */
	private LTL2FOLTranslator(boolean has_past, boolean has_loop) {
		super(new HashSet<Node>());
		this.has_always = has_loop;
		this.has_past = has_past;
	}

	/**
	 * Converts an LTL temporal formula into a regular Kodkod FOL formula. Uses the
	 * visitor to convert and adds any trace constraint left at the top level to
	 * handle nested post operators. It also adds the constraints that define the
	 * structure of the time relation constants. This is the main method that should
	 * be called to convert temporal formulas. The formula should be in negative
	 * normal form in order for the temporal quantifiers to be correctly translated.
	 * Optimizations will be applied if the the formula is known to force a loop or
	 * has no past operators.
	 * 
	 * @param form
	 *            the LTL formula to be converted.
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 * @return the resulting FOL formula.
	 */
	public static Formula translate(Formula form, boolean has_past, boolean has_loop) {
		LTL2FOLTranslator translator = new LTL2FOLTranslator(has_past, has_loop);

		Variable v = Variable.unary("v");
		Formula order_unr_trace1 = v.join(PREFIX).one().forAll(v.oneOf(STATE.difference(LAST)));
		Formula order_unr_trace2 = PREFIX.join(v).one().forAll(v.oneOf(STATE.difference(FIRST)));
		Formula order_unr_trace3 = FIRST.join(PREFIX.reflexiveClosure()).eq(STATE);

		Formula loopDecl_unr;
		if (!has_loop)
			loopDecl_unr = LOOP.lone();
		else
			loopDecl_unr = INFINITE;

		if (!has_loop) // otherwise already exactly bound
			loopDecl_unr = loopDecl_unr.and(LAST.one());

		translator.resetPostVariables();
		translator.pushVariable();

		Formula result = form.accept(translator);
		// this is needed for top level expressions
		if (translator.maxPrimeDepth > 0 && !has_loop) {
			Formula exists = translator.forceNextExists(FIRST, translator.maxPrimeDepth);
			result = exists.and(result);
		}

		return Formula.and(result, loopDecl_unr, order_unr_trace1, order_unr_trace2, order_unr_trace3);
	}

	/**
	 * Converts an LTL temporal expression into a regular Kodkod FOL expression in a
	 * concrete time step, counting from the {@link TemporalTranslator#FIRST
	 * initial} time. Uses the visitor to convert. This is the main method that
	 * should be called to convert temporal expressions.
	 * 
	 * @param expr
	 *            the LTL expression to be converted.
	 * @param state
	 *            the concrete state on which to evaluate the expression.
	 * @param has_past
	 *            whether the formula has past operators.
	 * @param has_loop
	 *            whether the formula is known to force a loop.
	 * @return the resulting static expression.
	 */
	public static Expression translate(Expression expr, int state, boolean has_past, boolean has_loop) {
		LTL2FOLTranslator translator = new LTL2FOLTranslator(has_past, has_loop);

		translator.resetPostVariables();
		translator.pushVariable(state);

		Expression result = expr.accept(translator);

		return result;
	}

	@Override
	public Expression visit(ConstantExpression constant) {
		maxPrimeDepth = curPrimeDepth > maxPrimeDepth ? curPrimeDepth : maxPrimeDepth;
		return constant;
	}

	@Override
	public Expression visit(Relation relation) {
		maxPrimeDepth = curPrimeDepth > maxPrimeDepth ? curPrimeDepth : maxPrimeDepth;
		if (TemporalTranslator.isTemporal(relation)) {
			if (has_past)
				return ((VarRelation) relation).expanded.join(getVariable().join(UNROLL_MAP));
			else
				return ((VarRelation) relation).expanded.join(getVariable());
		} else
			return relation;
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (TemporalTranslator.isTemporal(relationPredicate))
			// // cannot simply expand since it would loose symmetry breaking
			// return relationPredicate.toConstraints().always().accept(this);
			throw new UnsupportedOperationException("Total orders over variable relations still no supported.");
		else
			return relationPredicate;
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		int tempC = curPrimeDepth;
		int tempM = maxPrimeDepth;
		resetPostVariables();
		pushOperator(unaryTempFormula.op());
		pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = getQuantifier(getOperator(), e, maxPrimeDepth);
		popOperator();
		popVariable();
		curPrimeDepth = tempC;
		maxPrimeDepth = tempM;
		return rt;
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		int temp = curPrimeDepth;
		int tempM = maxPrimeDepth;

		pushOperator(binaryTempFormula.op());
		pushVariable();
		int quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		Formula rt, left, right;
		switch (binaryTempFormula.op()) {
		case UNTIL:
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPrimeDepth;
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = maxPrimeDepth;
			rt = getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			popVariable();
			break;
		case RELEASE:
			resetPostVariables();
			Formula rightAlways = binaryTempFormula.right().accept(this);
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = maxPrimeDepth;
			pushVariable();
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPrimeDepth;
			rt = getQuantifierRelease(rightAlways, left, right, quantificationPostLeft, quantificationPostRight);
			popVariable();
			popVariable();
			break;
		case SINCE:
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPrimeDepth;
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = maxPrimeDepth;
			rt = getQuantifierSince(left, right, quantificationPostLeftf, quantificationPostRight);
			popVariable();
			break;
		case TRIGGER:
		default:
			throw new UnsupportedOperationException("Unsupported binary temporal operator:" + binaryTempFormula.op());
		}
		popVariable();
		popOperator();
		curPrimeDepth = temp;
		maxPrimeDepth = tempM;
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		curPrimeDepth++;
		pushOperator(tempExpression.op());
		pushVariable();

		Expression localExpression = tempExpression.expression().accept(this);
		popOperator();
		popVariable();
		curPrimeDepth--;
		return localExpression;
	}

	private Formula getQuantifierUntil(Formula left, Formula right, int postDepthLeft, int postDepthRight) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Formula nfleft = left;
		if (postDepthLeft > 0 && !has_always)
			nfleft = nfleft.and(forceNextExists(l, postDepthLeft));

		nfleft = nfleft.forAll(l.oneOf(upTo(getVariableLastQuantificationUntil(false), r, true, false)));

		nfleft = right.and(nfleft);

		if (postDepthRight > 0 && !has_always)
			nfleft = nfleft.and(forceNextExists(r, postDepthRight));

		return nfleft.forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(TRACE.reflexiveClosure())));
	}

	private Formula getQuantifierSince(Formula left, Formula right, int postDepthLeft, int postDepthRight) {
		Variable r = getVariableSince(true);
		Variable l = getVariableSince(false);
		Formula nfleft = left;
		if (postDepthLeft > 0 && !has_always)
			nfleft = nfleft.and(forceNextExists(l, postDepthLeft));

		nfleft = nfleft.forAll(l.oneOf(upTo(r, getVariableLastQuantificationUntil(false), false, true)));

		nfleft = right.and(nfleft);

		if (postDepthRight > 0 && !has_always)
			nfleft = nfleft.and(forceNextExists(r, postDepthRight));

		return nfleft
				.forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(TRACE.transpose().reflexiveClosure())));
	}

	private Expression upTo(Expression t1, Expression t2, boolean inc1, boolean inc2) {
		Formula c = t2.in(t1.join(PREFIX.reflexiveClosure()));
		Expression exp1 = inc1 ? PREFIX.reflexiveClosure() : PREFIX.closure();
		Expression exp2 = inc2 ? PREFIX.reflexiveClosure() : PREFIX.closure();
		Expression exp11 = inc1 ? TRACE.reflexiveClosure() : TRACE.closure();
		Expression exp12 = inc2 ? TRACE.reflexiveClosure() : TRACE.closure();
		Expression e1 = (t1.join(exp1)).intersection(t2.join(exp2.transpose()));
		Expression e21 = (t1.join(exp11)).intersection(t2.join(exp12.transpose()));
		Expression e22 = (t2.join(exp1)).intersection(t1.join(exp2.transpose()));
		Expression e2 = e21.difference(e22);
		return c.thenElse(e1, e2);
	}

	private Formula getQuantifierRelease(Formula always, Formula left, Formula right, int leftFormula,
			int rightFormula) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;

		alw = always.forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(TRACE.reflexiveClosure())));
		if (!has_always)
			alw = alw.and(INFINITE);

		nfleft = right;
		if (rightFormula > 0 && !has_always)
			nfleft = nfleft.and(forceNextExists(l, rightFormula));

		nfleft = nfleft.forAll(l.oneOf(upTo(getVariableLastQuantificationRelease(false, true), r, true, true)));

		nfright = left.and(nfleft);

		if (leftFormula > 0 && !has_always)
			nfright = nfright.and(forceNextExists(r, leftFormula));

		nfright = nfright
				.forSome(r.oneOf(getVariableLastQuantificationRelease(false, true).join(TRACE.reflexiveClosure())));

		return alw.or(nfright);
	}

	private Formula getQuantifier(TemporalOperator op, Formula e, int posts) {
		Variable v;
		Expression quantification = getVariableLastQuantification();
		switch (op) {
		case ALWAYS:
			v = (Variable) getVariable();
			return e.forAll(v.oneOf(quantification.join(TRACE.reflexiveClosure())));
		case EVENTUALLY:
			v = (Variable) getVariable();
			if (posts > 0 && !has_always)
				e = e.and(forceNextExists(v, posts));
			return e.forSome(v.oneOf(quantification.join(TRACE.reflexiveClosure())));
		case HISTORICALLY:
			v = (Variable) getVariable();
			if (posts > 0 && !has_always)
				e = e.and(forceNextExists(v, posts).and(e));
			return e.forAll(v.oneOf(quantification.join(PREFIX.transpose().reflexiveClosure())));
		case ONCE:
			v = (Variable) getVariable();
			if (posts > 0 && !has_always)
				e = e.and(forceNextExists(v, posts));
			return e.forSome(v.oneOf(quantification.join(PREFIX.transpose().reflexiveClosure())));
		case NEXT:
			Expression v1 = getVariable();
			if (posts > 0 && !has_always)
				e = e.and(forceNextExists(v1, posts));
			else if (!has_always)
				e = e.and(v1.some());
			return e;
		case PREVIOUS:
			Expression v2 = getVariable();
			e = v2.some().and(e);
			if (posts > 0 && !has_always)
				e = e.and(forceNextExists(v2, posts));
			return e;
		default:
			return e;
		}
	}

	/**
	 * Forces the n-th state after s to exist.
	 * 
	 * @param s
	 *            a state.
	 * @param n
	 *            the number of future steps.
	 * @return formula forcing the n-th state after s to exist.
	 */
	private Formula forceNextExists(Expression s, int n) {
		Expression e = s.join(TRACE);
		for (int i = 1; i < n; i++)
			e = e.join(TRACE);
		return e.some();
	}

	/**
	 * Resets the original values of the variable nested post operators
	 * accumulators. Should be called whenever a new temporal variable is
	 * quantified.
	 */
	private void resetPostVariables() {
		curPrimeDepth = 0;
		maxPrimeDepth = 0;
	}

	/* Operators Context */
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();

	private void pushOperator(TemporalOperator op) {
		operators.add(op);
	}

	private TemporalOperator getOperator() {
		return operators.get(operators.size() - 1);
	}

	private void popOperator() {
		operators.remove(operators.size() - 1);
	}

	/* Variables */
	private List<Expression> variables = new ArrayList<Expression>();
	private int totalVariablesIt = 0;

	private void pushVariable() {
		if (!thereAreVariables()) {
			variables.add(FIRST);
			return;
		}

		switch (getOperator()) {
		case NEXT:
		case PRIME:
			variables.add(getVariable().join(TRACE));
			break;
		case PREVIOUS:
			variables.add(getVariable().join(PREFIX.transpose()));
			break;
		default:
			Variable v = Variable.unary("t" + totalVariablesIt);
			variables.add(v);
			totalVariablesIt++;
		}
	}

	/**
	 * Used to initialize the translation at a time other than the initial one.
	 * 
	 * @param state
	 *            the step of the trace in which to start the translation.
	 */
	private void pushVariable(int state) {
		if (!thereAreVariables()) {
			Expression s = FIRST;
			for (int i = 0; i < state; i++)
				s = s.join(TRACE);
			variables.add(s);
		} else
			throw new UnsupportedOperationException("No more vars.");
	}

	private void popVariable() {
		variables.remove(variables.size() - 1);
	}

	private boolean thereAreVariables() {
		return !variables.isEmpty();
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

	private Variable getVariableSince(boolean sideIsRight) {
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

}
