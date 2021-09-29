package kodkod.examples.pardinus.target;

import kodkod.ast.*;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 *   EXPERIMENTAL: do not use without care
 * @author Tim Nelson
 */
public class GettingTraces {

    public static void main(String[] args) {
        Relation p = Relation.unary("P");
        Relation q = Relation.unary("Q");
        System.out.println(Arrays.toString(args));

        Set<Object> atoms = new HashSet<>();
        int NATOMS = 1;
        for (int i = 0; i < NATOMS; i++) {
            atoms.add("Atom"+i);
        }
        Universe u = new Universe(atoms);

        PardinusBounds pb = new PardinusBounds(u);
        pb.bound(p, u.factory().allOf(1));
        pb.bound(q, u.factory().allOf(1));

        Formula f = p.some().or(q.some());
        f = f.and(p.some().or(q.no()));
        f = f.and(p.no().or(q.some()));
        f = f.and(p.no().or(q.no()));
        System.out.println("formula = "+f);

        ///////////////////////////////////////////////////

        ExtendedOptions eo = new ExtendedOptions();
        eo.setRunTarget(false);

        // only (?) one that gives cores to Kodkod
        eo.setSolver(SATFactory.MiniSatProver);
        eo.setSymmetryBreaking(0);
        eo.setLogTranslation(2);
        eo.setCoreGranularity(2);
        eo.setBitwidth(1); // minimum allowable

        PardinusSolver s = new PardinusSolver(eo);

        ///////////////////////////////////////////////////

        // Note: new "Explorer" iterator vs. Kodkod
        Explorer<Solution> sols =  s.solveAll(f, pb);
        int count = 0;
        while(sols.hasNext()) {
            Solution sol = sols.next();

            if(sol.unsat()) {
                System.out.println(sol.outcome());
                System.out.println(sol.stats().primaryVariables());
                System.out.println(sol.stats().clauses());
                // ? will this affect the proof, or just the core?
                // lots of strategies: this one is guaranteed minimal
                // if slow, try HybridStrategy (not guaranteed min, but good effort)
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace trace = ohno.solver.proof();
                //System.out.println(trace);
                //System.out.println(trace.getClass());
                Iterator<Clause> it = trace.iterator();
                while (it.hasNext()) { // top level clauses
                    Clause c = it.next();
                    System.out.println(c);
                    System.out.println("  antes=");
                    Iterator<Clause> it2 = c.antecedents();
                    while(it2.hasNext()) {
                        System.out.println("    "+it2.next());
                    }

                }

            }

            count++;
            if(sol.sat()) {
                System.out.println("-------------------");
                System.out.println(sol.instance().relationTuples());
            }
        }
        System.out.println("total number of solutions iterated: "+count);
    }

    /**
     * Compute Hamming distance between target and instance given
     * Relations not in target aren't counted.
     *
     * @param pb
     * @param instance
     * @return
     */
    private static int computeDist(PardinusBounds pb, Instance instance) {
        int counter = 0;
        for(Relation r : pb.targets().keySet()) {
            for(Tuple t : pb.target(r)) {
                if(!instance.tuples(r).contains(t))
                    counter++;
            }
            for(Tuple t : instance.tuples(r)) {
                if(!pb.target(r).contains(t))
                    counter++;
            }
        }
        return counter;
    }
}
