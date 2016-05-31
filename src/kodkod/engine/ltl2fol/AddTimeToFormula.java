package kodkod.engine.ltl2fol;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

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
 * @author Eduardo Pessoa, Nuno Macedo
 *
 */
public class AddTimeToFormula extends AbstractReplacer {

	private int needToDeclarePostR;
	private int numberMaxOfnestedPlicas;
	private int numberMaxPlicasInit;;

	private Relation next;
	private Relation Time;
	private Relation init;
	private Relation end;

	private Formula infinite;
	
	private Map<String,Relation> relations;

	/** 
	 * The relations resulting from the extension of the variable relations.
	 * @return
	 */
	public Map<String,Relation> getExtendedVarRelations() {
		return relations;
	}

	public AddTimeToFormula(Relation time, Relation next, Relation init, Relation end, Formula infinite) {
		super(new HashSet<Node>());
		this.relations = new HashMap<String,Relation>();
		this.Time = time;
		this.next = next;
		this.init = init;
		this.end = end;
		this.infinite = infinite;
		this.initializePostVariables();
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
			return this.getRelation((VarRelation) relation).join(this.getVariable());
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
		int temp = this.needToDeclarePostR;
		int tempI = this.numberMaxOfnestedPlicas;
		this.initializePostVariables();
		this.pushOperator(unaryTempFormula.op());
		this.pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = this.getQuantifier(this.getOperator(), e, needToDeclarePostR);
		this.numberMaxOfnestedPlicas = tempI;
		this.needToDeclarePostR = temp;
		this.popOperator();
		this.popVariable();
		return rt;	
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		this.pushOperator(binaryTempFormula.op());
		this.pushVariable();
		int temp, tempI, quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		temp = this.needToDeclarePostR;
		tempI = this.numberMaxOfnestedPlicas;
		this.initializePostVariables();
		Formula rt, left, right;
		switch(binaryTempFormula.op()) {
		case UNTIL:
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.needToDeclarePostR;
			this.pushVariable();
			this.initializePostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = this.needToDeclarePostR;
			rt = this.getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			this.popVariable();
			break;
		case RELEASE:
			Formula rightAlways = binaryTempFormula.right().accept(this);
			this.pushVariable();
			this.initializePostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = this.needToDeclarePostR;
			this.initializePostVariables();
			this.pushVariable();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = this.needToDeclarePostR;
			rt = this.getQuantifierRelease(rightAlways, left, right, quantificationPostLeft, quantificationPostRight);
			this.popVariable();
			this.popVariable();
			break;
		default: throw new UnsupportedOperationException("Unsupported binary temporal operator:"+binaryTempFormula.op());
		}
		this.numberMaxOfnestedPlicas = tempI;
		this.needToDeclarePostR = temp;
		this.popVariable();
		this.popOperator();
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		this.pushOperator(TemporalOperator.POST);
		this.pushVariable();
		//condition to verify the number max of nested plicas!!
		if(tempExpression.expression() instanceof TempExpression){
			numberMaxOfnestedPlicas++;
		}else{
			if (numberMaxOfnestedPlicas>this.needToDeclarePostR){
				this.needToDeclarePostR = numberMaxOfnestedPlicas;
				numberMaxOfnestedPlicas=1;
			}
		}

		//if the context is not a temporal operator.
		if (this.getVariableLastQuantification() == init) {
			if (numberMaxOfnestedPlicas>this.numberMaxPlicasInit){
				this.numberMaxPlicasInit = numberMaxOfnestedPlicas;
			}
		}
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
			nfleft = (forceNextExists(l, quantificationLeft).and(left)).forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(next.closure().join(r))));
		} else {
			nfleft = left.forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure()).intersection(next.closure().join(r))));
		}

		if (quantificationRight>0) {
			return (forceNextExists(r, quantificationRight).and(right)).and(nfleft).forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		} else {
			return right.and(nfleft).forSome(r.oneOf(getVariableLastQuantificationUntil(false).join(next.reflexiveClosure())));
		}
	}

	public Formula getQuantifierRelease(Formula always, Formula left, Formula right, int leftFormula, int rightFormula) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;

		alw = infinite.and(always.forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()))));

		if (rightFormula>0) {
			nfleft = (forceNextExists(l, rightFormula).and(right)).forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		} else {
			nfleft = right.forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure()).intersection(next.reflexiveClosure().join(r))));
		}


		if (leftFormula >0) {
			nfright = (forceNextExists(r, leftFormula).and(left)).and(nfleft).forSome(r.oneOf(getVariableLastQuantificationRelease(false, true).join(next.reflexiveClosure())));
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
			return infinite.and(e.forAll(v.oneOf(quantification.join(next.reflexiveClosure()))));
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
	
	public Formula forceNextExists(Expression exp , int x){
		Expression e = exp.join(next);
		for (int i = 1;i < x;i++) {
			e = e.join(next);
		}
		return e.some();
	}

	//Initialize the original values of the variable needToDeclarePostR and numberMaxOfnestedPlicas
	public void initializePostVariables(){
		this.needToDeclarePostR = 0;
		this.numberMaxOfnestedPlicas = 1;
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

	/**
	 * Returns the static relation corresponding to the extension of a variable relation.
	 * Creates it first time.
	 * @param name
	 * @param v
	 * @return
	 */
	private Relation getRelation(VarRelation v) {
		Relation e = this.relations.get(v.name());
		if (e == null) {
			Relation varRelation = Relation.nary(v.name(), v.arity() + 1);
			this.relations.put(v.name(),varRelation);
			return varRelation;
		} else {
			return e;
		}
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
