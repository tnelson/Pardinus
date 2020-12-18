package kodkod.examples.pardinus.target;

import kodkod.ast.*;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.TargetOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.instance.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 *   The {@link NoRetargeting} class demonstrates the Retargeter interface of Pardinus.
 *   Concretely, a Retargeter allows a caller to control target-oriented
 *   model-finding's retargeting pattern from the default (target
 *   the last found instance) to any pattern desired. Here, we show just
 *   the empty retargeter, which keeps the target constant, resulting
 *   in an enumeration of instances that are of monotonically non-decreasing
 *   distance from the target.

 *   The demo sets up a target-oriented model-finding problem
 *   with 2 atoms and 3 unary relations: p, q, and r.
 *
 *   Target for p: both atoms present.
 *   Target for q: no atoms present.
 *   Target for r: (no target).
 *
 *   Constraint: all 3 relations are non-empty.
 *
 * @author Tim Nelson
 */
public class AccumulateTargets {

    public static void main(String[] args) {
        Relation p1 = Relation.unary("P1");
        Relation p2 = Relation.unary("P2");
        Relation p3 = Relation.unary("P3");
        Relation p4 = Relation.unary("P4");
        Relation preventTrivial = Relation.unary("preventTrivial");

        Set<Object> atoms = new HashSet<>();
        int NATOMS = 1;
        for (int i = 0; i < NATOMS; i++) {
            atoms.add("Atom"+i);
        }
        Universe u = new Universe(atoms);

        PardinusBounds pb = new PardinusBounds(u);
        pb.bound(p1, u.factory().allOf(1));
        pb.bound(p2, u.factory().allOf(1));
        pb.bound(p3, u.factory().allOf(1));
        pb.bound(p4, u.factory().allOf(1));
        pb.bound(preventTrivial, u.factory().allOf(1));

        // Target the empty instance *at first*
        pb.setTarget(p1, u.factory().noneOf(1));
        pb.setTarget(p2, u.factory().noneOf(1));
        pb.setTarget(p3, u.factory().noneOf(1));
        pb.setTarget(p4, u.factory().noneOf(1));

        // No constraints -- except one, to prevent
        //   this from being an (unsupported) trivial problem
        //Formula f = preventTrivial.no();
        Formula f = preventTrivial.no()
                // and mention all relations to prevent auto-removal
                .and(p1.eq(p1))
                .and(p2.eq(p2))
                .and(p3.eq(p3))
                .and(p4.eq(p4));
        System.out.println("formula = "+f);

        ///////////////////////////////////////////////////

        ExtendedOptions eo = new ExtendedOptions();
        eo.setRunTarget(true);
        eo.setSolver(SATFactory.PMaxSAT4J);
        // disable SB for this demo
        eo.setSymmetryBreaking(0);
        eo.setLogTranslation(0);
        eo.setBitwidth(1); // minimal bitwidth allowed
        eo.setRetargeter(new Retargeter() {
            boolean firstInstance = true;
            @Override
            public void retarget(Translation transl) {
                assert(transl.cnf() instanceof TargetSATSolver);
                TargetSATSolver tcnf = (TargetSATSolver)transl.cnf();
                assert(transl.options() instanceof ExtendedOptions);
                ExtendedOptions opts = (ExtendedOptions) transl.options();

                if(firstInstance) {
                    tcnf.clearTargets(); // stop targeting empty instance
                    System.out.println("First instance; clearing target");
                }
                firstInstance = false;

                // Anti-target the current instance
                // Crucially, do not clear prior targets, since we want
                //   to build up a field of pressure away from instances seen
                for(int i = 1; i <= transl.numPrimaryVariables(); i++) {
                    int tgt = tcnf.valueOf(i) ? -i : i;
                    tcnf.addTarget(tgt);
                    System.out.println("Added new target: "+tgt);
                }

            }
        });

        PardinusSolver s = new PardinusSolver(eo);

        ///////////////////////////////////////////////////

        // Note: new "Explorer" iterator vs. Kodkod
        Explorer<Solution> sols =  s.solveAll(f, pb);
        int count = 0;
        while(sols.hasNext()) {
            Solution sol = sols.next();
            count++;
            if(sol.sat()) {
                System.out.println("-------------------");
                System.out.println(sol.instance().relationTuples());
            }
        }
        if(count > 0) count--;
        System.out.println("total number of instances: "+count);
    }
}