package kodkod.examples.pardinus.target;

import kodkod.ast.*;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.proofExplanation.core.CNFUnitPropagator;
import kodkod.engine.proofExplanation.core.ReducedResolutionTrace;
import kodkod.engine.satlab.*;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;
import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;

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
        Relation r = Relation.unary("R");
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
        pb.bound(r, u.factory().allOf(1));

        // -- TN Formula
        /*
        Formula f = p.some().or(q.some());
        f = f.and(p.some().or(q.no()));
        f = f.and(p.no().or(q.some()));
        f = f.and(p.no().or(q.no()));
        System.out.println("formula = "+f);
         */




        // additional formula for testing: 1
        /*
        Formula f = p.some().or(r.no());
        f = f.and(q.some().or(r.some()).or(p.no()));
        */

        // additional formula for testing: 2

        /*
        Formula f = p.some().or(q.some());
        f.and(p.some().or(q.no()));
        f.and(q.no().or(r.some()));
        f.and(p.no().or(r.no()));
        f.and(q.some().or(r.no()));
        f.and(q.some().or(p.no()));
        f.and(q.no().or(r.no()));

         */



        // additional formula for testing: negation of 2

        /*
        Formula f = p.no().or(q.no());
        f.and(p.no().or(q.some()));
        f.and(q.some().or(r.no()));
        f.and(p.some().or(r.some()));
        f.and(q.no().or(r.some()));
        f.and(q.no().or(p.some()));
        f.and(q.some().or(r.some()));

         */





        // additional formula for testing: 3

        Formula f = p.some().or(q.some()).or(r.some());
        f.and(p.some().or(q.no()).or(r.no()));
        f.and(p.no().or(q.some()).or(r.no()));
        f.and(p.no().or(q.no()).or(r.no()));
        f.and(p.some().or(q.no()).or(r.some()));
        f.and(p.some().or(q.no()).or(r.some()));
        f.and(p.some().or(q.some()).or(r.no()));
        f.and(p.no().or(q.no()).or(r.some()));








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
                ResolutionTrace origTrace = ohno.solver.proof();
                Iterator<Clause> coreIt = origTrace.iterator();
                
                System.out.println("Original trace: ");
                while (coreIt.hasNext()) { // top level clauses
                    Clause c = coreIt.next();
                    if (c == null) {
                        continue;
                    }
                    System.out.println(c);
                    System.out.println("  antes=");
                    Iterator<Clause> it2 = c.antecedents();
                    while(it2.hasNext()) {
                        System.out.println("    " + it2.next());
                    }
                }
                System.out.println();

                // TODO: this construction w/ IntBitSet doesn't allow negations of literals=
                IntSet assumps = new IntBitSet(6);
                assumps.add(2);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                Iterator<Clause> reducedIt = reducedTrace.iterator();

                System.out.println("Reduced trace:");
                while (reducedIt.hasNext()) {
                    Clause c = reducedIt.next();
                    if (c == null) {
                        continue;
                    }
                    System.out.println(c);
                    System.out.println("  antes=");
                    Iterator<Clause> it2 = c.antecedents();
                    while(it2.hasNext()) {
                        System.out.println("    " + it2.next());
                    }
                }


                // building set of clauses from unsat core
                /*
                IntSet coreClauseIndices = trace.core();
                Set<Clause> coreClauses = new HashSet<>();
                IntIterator coreClauseIterator = coreClauseIndices.iterator();
                while (coreClauseIterator.hasNext()) {
                    int nextClauseIndex = coreClauseIterator.next();
                    Clause nextClause = trace.get(nextClauseIndex);
                    coreClauses.add(nextClause);
                }*/


                //System.out.println(trace);
                //System.out.println(trace.getClass());
                /*
                Iterator<Clause> it = reducedTrace.iterator();


                while (it.hasNext()) { // top level clauses
                    Clause c = it.next();
                    if (c == null) {
                        continue;
                    }
                    System.out.println(c);
                    System.out.println("  antes=");
                    Iterator<Clause> it2 = c.antecedents();
                    while(it2.hasNext()) {
                        System.out.println("    " + it2.next());
                    }
                }

                 */

                /*
                while (coreIt.hasNext()) {
                    Formula fmla = coreIt.next();
                    System.out.println(fmla);
                    BinaryFormula binFmla = (BinaryFormula) fmla;
                    System.out.println("left = " + binFmla.left());
                    System.out.println("right = " + binFmla.right());
                }*/

            }

            count++;
            if(sol.sat()) {
                System.out.println("-------------------");
                System.out.println(sol.instance().relationTuples());
            }

        }
        System.out.println("total number of solutions iterated: "+count);

        int[] resolveArr1 = { 1, 2, 3 };
        int[] resolveArr2 = { -2, -3, 4 };
        int[] resolveEx = LazyTrace.resolve(resolveArr1, true, resolveArr2, true);
        for (int i : resolveEx) {
            System.out.println(i);
        }


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
