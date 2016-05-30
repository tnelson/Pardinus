package kodkod.engine.ltl2fol;

import java.util.Arrays;
import java.util.Map;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.instance.Bounds;

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

    
    
    
    private Relation[] timeList;
    public Map<String,Relation> varExtendedRelationsList;

    private Formula formula;


    //final types

    private Formula nnfFormula;

    private Formula dynamicFormula;
    private Formula dynamicFormulaExpanded;

    private Formula staticFormula;

    private Set<Relation> dynamicRelations;
    private Set<Relation> staticRelations;

    private Bounds dynamicBounds;
    private Bounds staticBounds;


    public TemporalFormulaExtension(Formula f, Bounds bounds, int numberoftimes){
        this.formula=f;
        this.negativeNormalForm();
        this.formulaSlicing();
        this.temporalFormulaExtension();
        this.putTimeInList();
        Bounding bounding = new Bounding(bounds,numberoftimes,this.timeList,varExtendedRelationsList);
        this.staticBounds = bounding.getStaticBounds();
        this.dynamicBounds = bounding.getDynamicBounds();

//        p("DYNAMIC PART: \n"+this.dynamicFormulaExpanded+"\n"+bounding.getDynamicBounds().toString());
//        p("\n\nSTATIC PART: \n"+this.staticFormula.toString()+"\n"+bounding.getStaticBounds().toString());


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
        AddTimeToFormula addTimeToFormula =  new AddTimeToFormula(Time,nextt,init,end,infinite);
        Formula result = addTimeToFormula.convert(dynamicFormula);
        this.varExtendedRelationsList = addTimeToFormula.getExtendedVarRelations();
        this.dynamicFormulaExpanded = allStuff.and(result);
    }

    public void putTimeInList(){
        this.timeList = new Relation[6];
        this.timeList[0] = Time;
        this.timeList[1] = init;
        this.timeList[2] = end;
        this.timeList[3] = next;
        this.timeList[4] = loop;
        this.timeList[5] = nextt;
        this.dynamicRelations.addAll(Arrays.asList(this.timeList));
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
