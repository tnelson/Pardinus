package kodkod.engine.ltl2fol;

import kodkod.ast.*;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.ast.visitor.ReturnVisitor;
import static kodkod.ast.operator.FormulaOperator.AND;

import java.util.*;


// TODO: use Kodkod's FormulaFlattener to retrieve the top-level conjuncts
public class SlicingDynamicFormulas extends AbstractReplacer implements
		ReturnVisitor<Expression, Formula, Decls, IntExpression> {

	private enum Context {
		formulaAnalysis, formulaExpansion
	};

	private boolean varRelation = false;
	private List<Formula> dynamicFormulas;
	private List<Formula> staticFormulas;
	private Context context;

	private Set<Relation> dynamicRelations;
	private Set<Relation> staticRelations;
	private Set<Relation> temporalRelationsList;

	public SlicingDynamicFormulas() {
		super(new HashSet<Node>());
		this.dynamicFormulas = new ArrayList<Formula>();
		this.staticFormulas = new ArrayList<Formula>();
		this.context = Context.formulaExpansion;
		this.dynamicRelations = new HashSet<Relation>();
		this.staticRelations = new HashSet<Relation>();
		this.temporalRelationsList = new HashSet<Relation>();
	}

	public Set<Relation> getDynamicRelations() {
		return dynamicRelations;
	}

	public Set<Relation> getStaticRelations() {
		return staticRelations;
	}

	public List<Formula> getDynamicFormulas() {
		return dynamicFormulas;
	}

	public List<Formula> getStaticFormulas() {
		return staticFormulas;
	}

	@Override
	public Expression visit(Relation relation) {
		this.temporalRelationsList.add(relation);
		if (relation instanceof VarRelation) {
			this.varRelation = true;
		}
		return relation;
	}

	@Override
	public Formula visit(NaryFormula naryFormula) {
		Formula[] arrayOfFormula = new Formula[naryFormula.size()];
		for (int j = 0; j < arrayOfFormula.length; j++) {
			Formula localFormula2 = naryFormula.child(j);
			if (context == Context.formulaExpansion) {
				if (((localFormula2 instanceof BinaryFormula) && ((BinaryFormula) localFormula2).op() == AND)
						|| (localFormula2 instanceof NaryFormula && ((NaryFormula) localFormula2).op() == AND)) {
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				} else {
					context = Context.formulaAnalysis;
					this.temporalRelationsList = new HashSet<Relation>();
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
					context = Context.formulaExpansion;
					if (varRelation) {
						this.varRelation = false;
						this.dynamicFormulas.add(arrayOfFormula[j]);
						this.dynamicRelations.addAll(this.temporalRelationsList);
					} else {
						this.staticRelations.addAll(this.temporalRelationsList);
						this.staticFormulas.add(arrayOfFormula[j]);
					}
				}
			} else {
				arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
			}
		}
		return Formula.compose(naryFormula.op(), arrayOfFormula);

	}

	@Override
	public Formula visit(BinaryFormula binaryFormula) {
		Formula left;
		Formula right;
		if (context == Context.formulaExpansion && binaryFormula.op() == AND) {
			if ((binaryFormula.left() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.left()).op() == AND)
					|| (binaryFormula.left() instanceof NaryFormula && ((NaryFormula) binaryFormula.left()).op() == AND)) {
				left = binaryFormula.left().accept(this);
			} else {
				context = Context.formulaAnalysis;
				this.temporalRelationsList = new HashSet<Relation>();
				left = binaryFormula.left().accept(this);
				context = Context.formulaExpansion;
				if (varRelation) {
					this.dynamicRelations.addAll(this.temporalRelationsList);
					this.varRelation = false;
					this.dynamicFormulas.add(left);
				} else {
					this.staticRelations.addAll(this.temporalRelationsList);
					this.staticFormulas.add(left);
				}
			}

			if ((binaryFormula.right() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.right()).op() == AND)
					|| (binaryFormula.right() instanceof NaryFormula && ((NaryFormula) binaryFormula.right()).op() == AND)) {
				right = binaryFormula.right().accept(this);
			} else {
				context = Context.formulaAnalysis;
				this.temporalRelationsList = new HashSet<Relation>();
				right = binaryFormula.right().accept(this);
				context = Context.formulaExpansion;
				if (varRelation) {
					this.varRelation = false;
					this.dynamicFormulas.add(right);
					this.dynamicRelations.addAll(this.temporalRelationsList);
				} else {
					this.staticRelations.addAll(this.temporalRelationsList);
					this.staticFormulas.add(right);
				}
			}

		} else {
			left = binaryFormula.left().accept(this);
			right = binaryFormula.right().accept(this);
		}
		return left.compose(binaryFormula.op(), right);

	}

}
