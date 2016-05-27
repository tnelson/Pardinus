package kodkod.engine.ltl2fol;


        import kodkod.ast.*;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.visitor.ReturnVisitor;
import static kodkod.ast.operator.FormulaOperator.AND;

import java.util.*;

public class SlicingDynamicFormulas implements ReturnVisitor<Expression, Formula, Decls, IntExpression> {

    private enum Context  {formulaAnalysis,formulaExpansion};



    private boolean varRelation  = false;
    private List<Formula> dynamicFormulas;
    private List<Formula> staticFormulas;
    private Context context;


    private Set<Relation> dynamicRelations;
    private Set<Relation> staticRelations;
    private Set<Relation> temporalRelationsList;


    public SlicingDynamicFormulas() {
        this.dynamicFormulas = new ArrayList<Formula>();
        this.staticFormulas = new ArrayList<Formula>();
        this.context = Context.formulaExpansion;
        this.dynamicRelations =  new HashSet<Relation>();
        this.staticRelations  = new HashSet<Relation>();
        this.temporalRelationsList =  new HashSet<Relation>();
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
    public Decls visit(Decls decls) {
        Decls localDecls = null;
        int i = 1;
        for (Decl localDecl1 : decls) {
            Decl localDecl2 = (Decl) visit(localDecl1);
            localDecls.and(localDecl2);
        }
        return localDecls;
    }

    @Override
    public Decls visit(Decl decl) {
        Variable localVariable = (Variable) decl.variable().accept(this);
        Expression localExpression = (Expression) decl.expression().accept(this);
        return localVariable.declare(decl.multiplicity(), localExpression);

    }

    @Override
    public Expression visit(Relation relation) {
        this.temporalRelationsList.add(relation);
        if(relation instanceof VarRelation){
          this.varRelation = true;
        }
        return relation;
    }

    @Override
    public Expression visit(Variable variable) {
        return variable;
    }

    @Override
    public Expression visit(ConstantExpression constantExpression) {
        return constantExpression;
    }

    @Override
    public Expression visit(UnaryExpression unaryExpression) {
        Expression localExpression2 = unaryExpression.expression().accept(this);
        return localExpression2.apply(unaryExpression.op());

    }

    @Override
    public Expression visit(BinaryExpression binaryExpression) {

        Expression right = binaryExpression.right().accept(this);
        Expression left = binaryExpression.left().accept(this);

        BinaryExpression binaryExpression1 = (BinaryExpression) left.compose(binaryExpression.op(), right);
        return binaryExpression1;
    }

    @Override
    public Expression visit(NaryExpression naryExpression) {
        Expression[] arrayOfExpression = new Expression[naryExpression.size()];
        int i = 1;
        for (int j = 0; j < arrayOfExpression.length; j++) {
            Expression localExpression2 = naryExpression.child(j);
            arrayOfExpression[j] = ((Expression) localExpression2.accept(this));
        }
        return Expression.compose(naryExpression.op(), arrayOfExpression);
    }

    @Override
    public Expression visit(Comprehension comprehension) {
        Decls localDecls = (Decls) comprehension.decls().accept(this);
        Formula localFormula = (Formula) comprehension.formula().accept(this);

        return localFormula.comprehension(localDecls);
    }

    @Override
    public Expression visit(IfExpression ifExpression) {
        Formula localFormula = (Formula) ifExpression.condition().accept(this);
        Expression localExpression2 = (Expression) ifExpression.thenExpr().accept(this);
        Expression localExpression3 = (Expression) ifExpression.elseExpr().accept(this);
        return localFormula.thenElse(localExpression2, localExpression3);
    }

    @Override
    public Expression visit(ProjectExpression projectExpression) {
        Expression localExpression2 = (Expression) projectExpression.expression().accept(this);
        IntExpression[] arrayOfIntExpression = new IntExpression[projectExpression.arity()];
        int j = 0;
        for (int k = projectExpression.arity(); j < k; j++) {
            arrayOfIntExpression[j] = ((IntExpression) projectExpression.column(j).accept(this));
        }
        return localExpression2.project(arrayOfIntExpression);

    }

    @Override
    public Expression visit(IntToExprCast intToExprCast) {
        IntExpression localIntExpression = (IntExpression) intToExprCast.intExpr().accept(this);
        return localIntExpression.cast(intToExprCast.op());

    }

    @Override
    public IntExpression visit(IntConstant intConstant) {
        return intConstant;
    }

    @Override
    public IntExpression visit(IfIntExpression ifIntExpression) {
        Formula localFormula = (Formula) ifIntExpression.condition().accept(this);
        IntExpression localIntExpression2 = (IntExpression) ifIntExpression.thenExpr().accept(this);
        IntExpression localIntExpression3 = (IntExpression) ifIntExpression.elseExpr().accept(this);

        return localFormula.thenElse(localIntExpression2, localIntExpression3);

    }

    @Override
    public IntExpression visit(ExprToIntCast exprToIntCast) {
        Expression localExpression = (Expression) exprToIntCast.expression().accept(this);
        return localExpression.apply(exprToIntCast.op());

    }

    @Override
    public IntExpression visit(NaryIntExpression naryIntExpression) {
        IntExpression[] arrayOfIntExpression = new IntExpression[naryIntExpression.size()];
        for (int j = 0; j < arrayOfIntExpression.length; j++) {
            IntExpression localIntExpression2 = naryIntExpression.child(j);
            arrayOfIntExpression[j] = ((IntExpression) localIntExpression2.accept(this));
        }
        return IntExpression.compose(naryIntExpression.op(), arrayOfIntExpression);
    }

    @Override
    public IntExpression visit(BinaryIntExpression binaryIntExpression) {
        IntExpression localIntExpression2 = (IntExpression) binaryIntExpression.left().accept(this);
        IntExpression localIntExpression3 = (IntExpression) binaryIntExpression.right().accept(this);

        return localIntExpression2.compose(binaryIntExpression.op(), localIntExpression3);
    }

    @Override
    public IntExpression visit(UnaryIntExpression unaryIntExpression) {
        IntExpression localIntExpression2 = (IntExpression) unaryIntExpression.intExpr().accept(this);
        return localIntExpression2.apply(unaryIntExpression.op());

    }

    @Override
    public IntExpression visit(SumExpression sumExpression) {
        Decls localDecls = (Decls) sumExpression.decls().accept(this);
        IntExpression localIntExpression2 = (IntExpression) sumExpression.intExpr().accept(this);

        return localIntExpression2.sum(localDecls);

    }

    @Override
    public Formula visit(IntComparisonFormula intComparisonFormula) {
        IntExpression localIntExpression1 = (IntExpression) intComparisonFormula.left().accept(this);
        IntExpression localIntExpression2 = (IntExpression) intComparisonFormula.right().accept(this);
        return localIntExpression1.compare(intComparisonFormula.op(), localIntExpression2);
    }

    @Override
    public Formula visit(QuantifiedFormula quantifiedFormula) {
        Decls f1 = quantifiedFormula.decls().accept(this);
        Formula f = quantifiedFormula.formula().accept(this);
        return (QuantifiedFormula) f.quantify(quantifiedFormula.quantifier(), f1);
    }

    @Override
    public Formula visit(NaryFormula naryFormula) {
        Formula[] arrayOfFormula = new Formula[naryFormula.size()];
        for (int j = 0; j < arrayOfFormula.length; j++) {
            Formula localFormula2 = naryFormula.child(j);
            if(context == Context.formulaExpansion){
                if(     ((localFormula2 instanceof BinaryFormula) && ((BinaryFormula) localFormula2).op() == AND) ||
                        (localFormula2 instanceof NaryFormula && ((NaryFormula) localFormula2).op() == AND )){
                    arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
                }else{
                    context = Context.formulaAnalysis;
                    this.temporalRelationsList =  new HashSet<Relation>();
                    arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
                    context = Context.formulaExpansion;
                    if(varRelation){this.varRelation = false;
                        this.dynamicFormulas.add(arrayOfFormula[j]);
                        this.dynamicRelations.addAll(this.temporalRelationsList);
                    }
                    else{
                        this.staticRelations.addAll(this.temporalRelationsList);
                        this.staticFormulas.add(arrayOfFormula[j]);
                    }
                }
            }else{
                arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
            }
        }
        return Formula.compose(naryFormula.op(), arrayOfFormula);

    }

    @Override
    public Formula visit(BinaryFormula binaryFormula) {
        Formula left;
        Formula right;
        if(context == Context.formulaExpansion && binaryFormula.op() == AND) {
            if (    (binaryFormula.left() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.left()).op() == AND) ||
                    (binaryFormula.left() instanceof NaryFormula && ((NaryFormula) binaryFormula.left()).op() == AND )) {
                left = binaryFormula.left().accept(this);
            } else {
                context = Context.formulaAnalysis;
                this.temporalRelationsList =  new HashSet<Relation>();
                left = binaryFormula.left().accept(this);
                context = Context.formulaExpansion;
                if(varRelation){
                    this.dynamicRelations.addAll(this.temporalRelationsList);
                    this.varRelation = false;this.dynamicFormulas.add(left);
                }
                else{
                    this.staticRelations.addAll(this.temporalRelationsList);
                    this.staticFormulas.add(left);
                }
            }


            if (    (binaryFormula.right() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.right()).op() == AND ) ||
                    (binaryFormula.right() instanceof NaryFormula && ((NaryFormula) binaryFormula.right()).op() == AND )) {
                right = binaryFormula.right().accept(this);
            }
            else {
                context = Context.formulaAnalysis;
                this.temporalRelationsList =  new HashSet<Relation>();
                right = binaryFormula.right().accept(this);
                context = Context.formulaExpansion;
                if(varRelation){this.varRelation = false;this.dynamicFormulas.add(right);
                    this.dynamicRelations.addAll(this.temporalRelationsList);
                }
                else{
                    this.staticRelations.addAll(this.temporalRelationsList);
                    this.staticFormulas.add(right);
                }
            }

        }else{
             left = binaryFormula.left().accept(this);
             right = binaryFormula.right().accept(this);
        }
        return left.compose(binaryFormula.op(), right);


    }

    @Override
    public Formula visit(NotFormula notFormula) {

        Formula f = notFormula.formula().accept(this);
        return f.not();
    }

    @Override
    public Formula visit(ConstantFormula constantFormula) {

        return constantFormula;
    }

    @Override
    public Formula visit(ComparisonFormula comparisonFormula) {
        Expression left;
        Expression right;
        left = comparisonFormula.left().accept(this);
        right = comparisonFormula.right().accept(this);

        return left.compare(comparisonFormula.op(), right);

    }

    @Override
    public Formula visit(MultiplicityFormula multiplicityFormula) {
        Expression localExpression = (Expression) multiplicityFormula.expression().accept(this);
        return localExpression.apply(multiplicityFormula.multiplicity());
    }

    @Override
    public Formula visit(RelationPredicate relationPredicate) {

        final Relation r = (Relation) relationPredicate.relation().accept(this);
        Formula localFormula;
        switch (relationPredicate.name()) {
            case ACYCLIC:
                localFormula = r.acyclic();
                break;
            case FUNCTION:
                final RelationPredicate.Function fp = (RelationPredicate.Function) relationPredicate;
                final Expression domain = fp.domain().accept(this);
                final Expression range = fp.range().accept(this);
                if (fp.targetMult() == Multiplicity.ONE) {
                    localFormula = r.function(domain, range);
                } else {
                    localFormula = r.partialFunction(domain, range);
                }

                break;
            case TOTAL_ORDERING:
                final RelationPredicate.TotalOrdering tp = (RelationPredicate.TotalOrdering) relationPredicate;
                final Relation ordered = (Relation) tp.ordered().accept(this);
                final Relation first = (Relation) tp.first().accept(this);
                final Relation last = (Relation) tp.last().accept(this);
                localFormula = r.totalOrder(ordered, first, last);
                break;
            default:
                throw new IllegalArgumentException("unknown relation predicate: " + relationPredicate.name());
        }

        return localFormula;


    }


    @Override
    public Formula visit(UnaryTempFormula unaryTempFormula) {
        Formula f = unaryTempFormula.formula().accept(this);
        return f.compose(unaryTempFormula.op());
    }

    @Override
    public Formula visit(BinaryTempFormula binaryTempFormula) {
        Formula left = binaryTempFormula.left().accept(this);
        Formula right = binaryTempFormula.right().accept(this);
        return left.compose(binaryTempFormula.op(),right);
    }

    @Override
    public Expression visit(TempExpression tempExpression) {
        Expression localExpression2 = tempExpression.expression().accept(this);
        return localExpression2.post();
    }
}




























