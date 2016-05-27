package kodkod.engine.ltl2fol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ConstantFormula;
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
 * Created by macbookpro on 14/03/16.
 */
public class AddTimeToFormula extends AbstractReplacer {

	private int needToDeclarePostR;

	private Relation next;
	private Relation Time;
	private Relation init;
	private Relation end;

	private Formula infinite;
	
	private Set<VarRelation> relations;

	public Set<VarRelation> getVarRelations() {
		return relations;
	}

	public AddTimeToFormula(Relation time, Relation next, Relation init, Relation end, Formula infinite) {
		super(new HashSet<Node>());
		this.relations = new HashSet<VarRelation>();
		this.Time = time;
		this.next = next;
		this.init = init;
		this.end = end;
		this.infinite = infinite;
		pushVariable();
	}

    public Formula convert(Formula f){
        Formula result = f.accept(this);
        if (needToDeclarePostR > 0)
			return forceNextExists(init, needToDeclarePostR).and(result);
		else
			return result;
    }
	
    @Override
	public Expression visit(Relation relation) {
		if (isTemporal(relation))
			return this.getRelation(relation.name(), relation).join(this.getVariable());
		else return relation;
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (isTemporal(relationPredicate))
			return relationPredicate.toConstraints().accept(this);
		else return relationPredicate;
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		int temp = needToDeclarePostR;
		needToDeclarePostR = 0;
		this.pushOperator(unaryTempFormula.op());
		this.pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = this.getQuantifier(this.getOperator(), e, needToDeclarePostR);
		needToDeclarePostR = temp;
		this.popOperator();
		this.popVariable();
		return rt;	
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		this.pushOperator(binaryTempFormula.op());
		this.pushVariable();
		int temp, quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		Formula rt, left, right;
		switch(binaryTempFormula.op()) {
		case UNTIL:
			temp = needToDeclarePostR;
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.needToDeclarePostR;
			this.needToDeclarePostR = temp;
			this.pushVariable();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = this.needToDeclarePostR;
			this.needToDeclarePostR = temp;
			rt = this.getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			this.popVariable();
			break;
		case RELEASE:
			temp = needToDeclarePostR;
			Formula rightAlways = binaryTempFormula.right().accept(this);
			int quantificationPostRightAlways = this.needToDeclarePostR;
			this.needToDeclarePostR = temp;
			this.pushVariable();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = this.needToDeclarePostR;
			this.needToDeclarePostR = temp;
			this.pushVariable();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.needToDeclarePostR;
			this.needToDeclarePostR = temp;
			rt = this.getQuantifierRelease(rightAlways, left, right, quantificationPostRightAlways, quantificationPostLeft, quantificationPostRight);
			this.popVariable();
			this.popVariable();
			break;
		default: throw new UnsupportedOperationException("Unsupported binary temporal operator:"+binaryTempFormula.op());
		}
		this.popVariable();
		this.popOperator();
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		this.pushOperator(TemporalOperator.POST);
		this.pushVariable();
		this.needToDeclarePostR++;
		Expression localExpression2 = tempExpression.expression().accept(this);
		this.popOperator();
		this.popVariable();
		return localExpression2;
	}

	public Formula getQuantifierUntil(Formula left, Formula right, int quantificationLeft, int quantificationRight) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Formula nfleft;
		if (quantificationLeft>0) {
			nfleft = l.join(next).some().and(left).forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(next.closure().join(r))));
		} else {
			nfleft = left.forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(next.closure().join(r))));
		}

		if (quantificationRight>0) {
			return r.join(next).some().and(right).and(nfleft).forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		} else {
			return right.and(nfleft).forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		}
	}

	public Formula getQuantifierRelease(Formula always, Formula left, Formula right, int rightFormulaAlways, int leftFormula, int rightFormula) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;
		if (rightFormulaAlways>0) { // desnecessario! infinite => G some next 
			alw = infinite.and(v.join(next).some().and(always).forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()))));
		} else {
			alw = infinite.and(always.forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()))));
		}


		if (rightFormula>0) {
			nfleft = l.join(next).some().and(right).forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		} else {
			nfleft = right.forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		}


		if (leftFormula>0) {
			nfright = r.join(next).some().and(left).and(nfleft).forSome(r.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure())));
		} else {
			nfright = left.and(nfleft).forSome(r.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure())));
		}
		return alw.or(nfright);
	}

	public Formula getQuantifier(TemporalOperator op, Formula e, int posts) {
		Variable v;
		Expression quantification = this.getVariableLastQuantification();
		switch(op) {
		case ALWAYS:
			v = (Variable) getVariable();
			if (posts>0) { // desnecessario! infinite => G some next 
				return infinite.and(forceNextExists(v, posts).and(e).forAll(v.oneOf(quantification.join(next.reflexiveClosure()))));
			} else {
				return infinite.and(e.forAll(v.oneOf(quantification.join(next.reflexiveClosure()))));
			}
		case EVENTUALLY:
			v = (Variable) getVariable();
			if (posts>0) {
				return forceNextExists(v, posts).and(e).forSome(v.oneOf(quantification.join(next.reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(next.reflexiveClosure())));
			}
		case HISTORICALLY:
			v = (Variable) getVariable();
			if (posts>0) {
				return forceNextExists(v, posts).and(e).forAll(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			} else {
				return e.forAll(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			}
		case ONCE:
			v = (Variable) this.getVariable();
			if (posts>0) {
				return forceNextExists(v, posts).and(e).forSome(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(next.transpose().reflexiveClosure())));
			}
		case NEXT:
		case PREVIOUS:
			Expression v1 = this.getVariable();
			if (posts>0) {
				return forceNextExists(v1, posts).and(v1.some().and(e));
			} else {
				return v1.some().and(e);
			}
		default:
			return e;
		}
	}
	
	private Formula forceNextExists(Expression v, int n) {
		Formula res = ConstantFormula.TRUE;
		Expression aux = v;
		for (int i = 1; i <= n; i++) {
			for (int j = 0; j < i; j++)
				aux = aux.join(next);
			res = res.equals(ConstantFormula.TRUE)?aux.some():res.and(aux.some());
			aux = v;
		}
		return res;
	}


	/*Operators Context*/
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();
	private int totalOperators = -1;

	public void pushOperator(TemporalOperator op) {
		this.totalOperators++;
		this.operators.add(op);
	}

	public TemporalOperator getOperator() {
		return this.operators.get(this.totalOperators);
	}

	public boolean thereAreOperator() {
		if (this.operators.size() == 0) return false;
		return true;
	}

	public void popOperator() {
		this.operators.remove(this.totalOperators);
		this.totalOperators--;
	}

	/*VarRelations*/

	private VarRelation getRelation(String name, Relation v) {
		VarRelation e = this.getRelationFromName(name);
		if (e == null) {
			VarRelation varRelation = VarRelation.nary(name, v.arity() + 1);
			this.relations.add(varRelation);
			return varRelation;
		} else {
			return e;
		}
	}

	private VarRelation getRelationFromName(String name) {
		Iterator it = this.relations.iterator();
		while (it.hasNext()) {
			VarRelation aux = (VarRelation) it.next();
			if (aux.name().equals(name)) return aux;
		}
		return null;
	}


	/*Variables*/
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
		if (this.totalVar > 0) this.totalVar--;
	}

	private boolean thereAreVariables() {
		if (this.variables.size() == 0) return false;
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
