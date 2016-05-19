package kodkod.pardinus.temporal;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * Created by Eduardo Pessoa on 20/03/16.
 */
public class TemporalFormulaExtension {

    private Relation Time = Relation.unary("Time");
    private Relation init = Relation.unary("init");
    private Relation end = Relation.unary("end");
    private Relation next = Relation.binary("next");



    private Relation nextt = Relation.binary("nextt");
    private Relation loop = Relation.nary("loop", 2);

    Formula order = next.totalOrder(Time, init, end);
    Formula loopDecl =  loop.partialFunction(end,Time);
    Expression nextDecl = next.union(loop);
    Formula nextFnct = nextt.eq(nextDecl);

    Formula allStuff = Formula.and(order, loopDecl,  nextFnct);

    Formula infinite = loop.one();

    
    
    
    private List<Relation> timeList;
    public Set<VarRelation> varRelationsList;

    private Formula formula;


    //final types

    private Formula nnfFormula;

    private Formula dynamicFormula;
    private Formula dynamicFormulaExpanded;

    private Formula staticFormula;



    private Set dynamicRelations;
    private Set staticRelations;

    private Bounds bounds;
    private Bounds dynamicBounds;
    private Bounds staticBounds;


    public TemporalFormulaExtension(Formula f, Bounds bounds, int numberoftimes){
        this.formula=f;
        this.negativeNormalForm();
        this.formulaSlicing();
        this.temporalFormulaExtension();
        this.putTimeInList();
        Bounding bounding = new Bounding(bounds,numberoftimes,this.timeList,varRelationsList,this.dynamicRelations);
        SplitBounds splitBounds = new SplitBounds(bounding.getDynamicRelations(),this.staticRelations,bounding.getBounds());
        this.staticBounds = splitBounds.getStaticBounds();
        this.dynamicBounds = splitBounds.getDynamicBounds();

        p("DYNAMIC PART: \n"+this.dynamicFormulaExpanded+"\n"+splitBounds.getDynamicBounds().toString());
        p("\n\nSTATIC PART: \n"+this.staticFormula.toString()+"\n"+splitBounds.getStaticBounds().toString());


    }

    public void negativeNormalForm(){
        NNFReplacer nnf = new NNFReplacer();
        this.nnfFormula = this.formula.accept(nnf);
    }

    public void formulaSlicing(){
        SlicingDynamicFormulas slicingDynamicFormulas =  new SlicingDynamicFormulas();
        this.nnfFormula.accept(slicingDynamicFormulas);
        this.dynamicFormula = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
        this.staticFormula = Formula.and(slicingDynamicFormulas.getStaticFormulas());
        this.dynamicRelations =  slicingDynamicFormulas.getDynamicRelations();
        this.staticRelations =  slicingDynamicFormulas.getStaticRelations();
    }


    public void temporalFormulaExtension(){
        AddTimeToFormula addTimeToFormula =  new AddTimeToFormula(Time,next,init,end,infinite);
        Formula result = addTimeToFormula.convert(dynamicFormula);
        this.varRelationsList = addTimeToFormula.getVarRelations();
        this.dynamicFormulaExpanded = allStuff.and(result);
    }

    public void putTimeInList(){
        this.timeList = new ArrayList<Relation>();
        this.timeList.add(Time);
        this.timeList.add(init);
        this.timeList.add(end);
        this.timeList.add(next);

        this.timeList.add(loop);
        this.timeList.add(nextt);
        this.dynamicRelations.addAll(this.timeList);
    }

    public Bounds getDynamicBounds() {
        return dynamicBounds;
    }

    public Bounds getStaticBounds() {
        return staticBounds;
    }

    public Formula getStaticFormula() {
        return staticFormula;
    }

    public Formula getDynamicFormula() {
        return dynamicFormulaExpanded;
    }

    public static void p(String name) {
        System.out.println(name);
    }


}
