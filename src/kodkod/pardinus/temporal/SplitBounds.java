package kodkod.pardinus.temporal;

import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.instance.Bounds;

import java.util.Iterator;
import java.util.Set;

/**
 * Created by macbookpro on 17/04/16.
 */
public class SplitBounds {

    private Bounds staticBounds;
    private Bounds dynamicBounds;


    private Set<Relation> dynamicRelations;
    private Set<Relation>  staticRelations;
    private Bounds bounds;

    public SplitBounds(Set dynamicRelations,Set staticRelations,Bounds bounds){
        this.dynamicRelations = dynamicRelations;
        this.staticRelations = staticRelations;
        this.bounds = bounds;

        this.staticBounds = new Bounds(this.bounds.universe());
        this.dynamicBounds = new Bounds(this.bounds.universe());
        this.splitBounds();
    }

    public Bounds getStaticBounds() {
        return staticBounds;
    }

    public Bounds getDynamicBounds() {
        return dynamicBounds;
    }

    public void splitBounds(){
        this.splitDynamicBounds();
        this.splitStaticBounds();
    }


    public void splitDynamicBounds(){

        for (Relation r : this.dynamicRelations){
            if (this.bounds.upperBound(r).equals(this.bounds.lowerBound(r))) {
                this.dynamicBounds.boundExactly(r, this.bounds.upperBound(r));
            } else {
                this.dynamicBounds.bound(r, this.bounds.upperBound(r));
            }
        }
    }

    public void splitStaticBounds(){
        for (Relation r : this.staticRelations){
            if (this.bounds.upperBound(r).equals(this.bounds.lowerBound(r))) {
                this.staticBounds.boundExactly(r, this.bounds.upperBound(r));
            } else {
                this.staticBounds.bound(r, this.bounds.upperBound(r));
            }
        }
    }
}
