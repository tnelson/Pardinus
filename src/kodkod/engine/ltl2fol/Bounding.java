package kodkod.engine.ltl2fol;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.instance.*;

import java.util.*;

/**
 * Created by Eduardo Pessoa on 20/03/16.
 */
public class Bounding {
    private Bounds oldBounds;

    private int numberOfTimes;

    private Universe universe;
    private TupleFactory tupleFactory;
    private Bounds bounds;
    private List<Relation> timedRelations;
    private Set<VarRelation> VarRelationsWithTime;


    private Set<Relation> dynamicRelationsOld;
    private Set<Relation> dynamicRelations;
    private List<Relation> tempDynamicRelations;


    public Bounding(Bounds oldBounds, int numberOfTimes, List<Relation> time, Set<VarRelation> varRelations,Set dynamicRelations) {
        this.oldBounds = oldBounds;
        this.numberOfTimes = numberOfTimes;
        this.timedRelations = time;
        this.VarRelationsWithTime = varRelations;
        this.dynamicRelationsOld = dynamicRelations;
        this.tempDynamicRelations = new ArrayList<Relation>();
        this.dynamicRelations =  new HashSet<Relation>();
        this.createUniverse();
        this.bounding();
        this.setVarRelationWithNewArity();
    }


    public Bounds getBounds() {
        return bounds;
    }

    public void bounding() {
        TupleSet tupleSetTime = this.tupleFactory.range(this.tupleFactory.tuple(new Object[]{"Time0"}), this.tupleFactory.tuple(new Object[]{"Time" + (this.numberOfTimes - 1)}));
        for (Relation r : this.oldBounds.upperBounds().keySet()) {
            if (r instanceof VarRelation) {
                if (oldBounds.upperBound(r).equals(oldBounds.lowerBound(r))) {
                    this.makeNewTuplesFromOldBounds(r.arity(),true,r,tupleSetTime,true);
                } else {
                    this.makeNewTuplesFromOldBounds(r.arity(),true,r,tupleSetTime,false);
                }
            } else {
                if (oldBounds.upperBound(r).equals(oldBounds.clone().lowerBound(r))) {
                   this.makeNewTuplesFromOldBounds(r.arity(),false,r,null,true);
                } else {
                    this.makeNewTuplesFromOldBounds(r.arity(),false,r,null,false);
                }
            }
        }

        bounds.bound(timedRelations.get(0), tupleSetTime);//Time
        bounds.bound(timedRelations.get(1), tupleSetTime);//init
        bounds.bound(timedRelations.get(2), tupleSetTime);//end
        bounds.bound(timedRelations.get(3), tupleSetTime.product(tupleSetTime));//next
        bounds.bound(timedRelations.get(4), tupleSetTime.product(tupleSetTime));//loop
        bounds.bound(timedRelations.get(5), tupleSetTime.product(tupleSetTime));//nextt
    }


    public Set<Relation> getDynamicRelations() {
        return this.dynamicRelations;
    }

    /*create new relations with new arity*/
    public void setVarRelationWithNewArity(){
        for (Relation rr : this.dynamicRelationsOld) {
            Relation rTemp = relationsExists(rr);
            this.dynamicRelations.add(rTemp);
        }
    }

    public Relation relationsExists(Relation rr){
        for (Relation r : this.tempDynamicRelations){
            if(r.name().equals(rr.name())){
                return r;
            }
        }
        return rr;
    }
    /*-------------------------*/


    public VarRelation getVarRelation(Relation r) {
        Iterator it = this.VarRelationsWithTime.iterator();
        while (it.hasNext()) {
            VarRelation relation = (VarRelation) it.next();
            if (relation.name().equals(r.name())) {
                this.tempDynamicRelations.add(relation);
                return relation;
            }
        }
        return null;
    }


    public void createUniverse() {
        ArrayList localArrayList = new ArrayList();
        Iterator it = this.oldBounds.universe().iterator();
        while (it.hasNext()) {
            localArrayList.add(it.next());
        }

        for (int i = 0; i < this.numberOfTimes; i++) {
            localArrayList.add("Time" + i);
        }

        this.universe = new Universe(localArrayList);
        this.tupleFactory = this.universe.factory();
        this.bounds = new Bounds(this.universe);
    }

    public void makeNewTuplesFromOldBounds(int arity,boolean isDinamicRelation, Relation relation,TupleSet tupleSetTime,boolean isExactlyBound) {
        TupleSet tupleSet  = this.tupleFactory.noneOf(arity);
        Iterator itr = oldBounds.clone().upperBounds().get(relation).iterator();
        while (itr.hasNext()) {
            Tuple t = (Tuple) itr.next();
            List l = new ArrayList();
            for (int i = 0; i < t.arity(); i++) {
                l.add(t.atom(i));
            }
            tupleSet.add(this.tupleFactory.tuple(l));
        }

        if(isDinamicRelation){
            if(isExactlyBound){bounds.boundExactly(this.getVarRelation(relation),tupleSet.product(tupleSetTime));}
            else{bounds.bound(this.getVarRelation(relation),tupleSet.product(tupleSetTime));}
        } else{
            if(isExactlyBound){bounds.boundExactly(relation,tupleSet);}
            else{bounds.bound(relation,tupleSet);}
        }

    }



}
