package kodkod.examples.pardinus.target;

import kodkod.ast.*;
import kodkod.ast.operator.Multiplicity;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.fol2sat.MemoryLogger;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.proofExplanation.core.CNFUnitPropagator;
import kodkod.engine.proofExplanation.core.ReducedResolutionTrace;
import kodkod.engine.proofExplanation.core.ReducedSATProver;
import kodkod.engine.satlab.*;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.engine.ucore.StrategyUtils;
import kodkod.instance.*;
import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;
import kodkod.util.nodes.AnnotatedNode;
import kodkod.util.nodes.Nodes;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

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

         */


        //System.out.println("formula = "+f);




        // additional formula for testing: 1
        /*
        Formula f = p.some().or(r.no());
        f = f.and(q.some().or(r.some()).or(p.no()));
        */

        // additional formula for testing: 2


        Formula f = p.some().or(q.some()); //
        f = f.and(p.some().or(q.no())); //
        f = f.and(q.no().or(r.some())); //
        f = f.and(p.no().or(r.no()));
        //f = f.and(q.some().or(r.no()));
        f = f.and(q.some().or(p.no()));
        //f = f.and(q.no().or(r.no()));

        Formula assumpF = p.no().and(r.no());

        /*
        Formula f = q.no().or(r.some());
        f = f.and(p.no().or(r.no()));
        f = f.and(q.some().or(p.no()));
         */


        // additional formula for testing: negation of 2

        /*
        Formula f = p.no().or(q.no());
        f = f.and(p.no().or(q.some()));
        f = f.and(q.some().or(r.no()));
        f = f.and(p.some().or(r.some()));
        f = f.and(q.no().or(r.some()));
        f = f.and(q.no().or(p.some()));
        f = f.and(q.some().or(r.some()));

         */

        // additional formula for testing: 3
        //Formula f = p.some().or(q.some()).or(r.some());

        // additional formula for testing: 4

        /*
        Formula f = p.some().or(q.some()).or(r.some());
        f = f.and(p.some().or(q.no()).or(r.no()));
        f = f.and(p.no().or(q.some()).or(r.no()));
        f = f.and(p.no().or(q.no()).or(r.no()));
        f = f.and(p.some().or(q.no()).or(r.some()));
        f = f.and(p.some().or(q.no()).or(r.some()));
        f = f.and(p.some().or(q.some()).or(r.no()));
        f = f.and(p.no().or(q.no()).or(r.some()));

         */






        ///////////////////////////////////////////////////

        ExtendedOptions eo = new ExtendedOptions();
        eo.setRunTarget(false);

        // only (?) one that gives cores to Kodkod
        eo.setSolver(SATFactory.MiniSatProver);
        eo.setSymmetryBreaking(0);
        eo.setLogTranslation(2);
        eo.setCoreGranularity(2);
        eo.setBitwidth(1); // minimum allowable

        Translation.Whole translation = Translator.translate(f, pb, eo);
        System.out.println("Translation map: ");
        for (Entry<Relation, IntSet> entry : translation.getPrimaryVariables().entrySet()) {
            System.out.println(entry.getKey() + " : " + entry.getValue());
        }
        Map<Relation, IntSet> primVars = translation.getPrimaryVariables();
        
        Set<Formula> assumpSet = Nodes.roots(assumpF);
        IntSet assumpIntSet = new IntTreeSet();

        for (Formula ff : assumpSet) {
            MultiplicityFormula mf = (MultiplicityFormula) ff;
            IntSet relIntSet = primVars.get(mf.expression());
            if (mf.multiplicity() == Multiplicity.NO) {
                for (IntIterator relIt = relIntSet.iterator(); relIt.hasNext(); ) {
                    assumpIntSet.add(-1 * relIt.next());
                }
            }
            if (mf.multiplicity() == Multiplicity.SOME) {
                for (IntIterator relIt = relIntSet.iterator(); relIt.hasNext(); ) {
                    assumpIntSet.add(relIt.next());
                }
            }
        }

        System.out.println("Original formula: " + f);
        System.out.println("assumption formula: " + assumpF);
        System.out.println("assumpIntSet: " + assumpIntSet);


        TranslationLog tlog = translation.log();

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

                //System.out.println("Assumption literals: " + assumpLits);
                IntSet assumps = new IntTreeSet();
                //assumps.add(-2);
                //assumps.add(3);
                assumps.add(1);
                assumps.add(2);
                //assumps.add(5);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumpIntSet);
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

                System.out.println("Reduced core: " + reducedTrace.core());

                //System.out.println("coreUnits on reducedTrace:" + StrategyUtils.coreUnits(reducedTrace));
                
                // TODO: fix current issue: StrategyUtils.coreUnits does not work on reducedTrace but DOES work on origTrace
                // I think this is because trace.reverseIterator(...) is fed trace.core() as an argument. does our 
                // ReducedResolutionTrace.reverseIterator(...) // ReducedResolutionTrace.core() interact with the original core?
                // yes: the latter definitely does. can we make the former do the same? 
                //     (it's a hack and not technically correct though.)
                

                ReducedSATProver rsp = new ReducedSATProver(reducedTrace);
                // TODO: where do I get log from in main?
                ResolutionBasedProof rbf = new ResolutionBasedProof(rsp, tlog);
                Map<Formula, Node> fnodeMap = rbf.highLevelCore();
                System.out.println("\nfnodeMap values: ");
                for (Node n : fnodeMap.values()) {
                    System.out.println(n);
                }

                /*
                System.out.println("\nReduced trace core:");
                IntSet rtCore = reducedTrace.core();
                for (IntIterator rtCoreIt = rtCore.iterator(); rtCoreIt.hasNext(); ) {
                    System.out.println(origTrace.get(rtCoreIt.next()));
                }

                System.out.println("\nReduced trace iterator behavior:");
                IntSet iteratorTestInts = new IntTreeSet();
                iteratorTestInts.add(0);
                iteratorTestInts.add(4);
                iteratorTestInts.add(2);
                for (Iterator<Clause> itTestIt = reducedTrace.reverseIterator(iteratorTestInts); itTestIt.hasNext(); ) {
                    System.out.println(itTestIt.next());
                }*/
            }

            count++;
            if(sol.sat()) {
                System.out.println("-------------------");
                System.out.println(sol.instance().relationTuples());
            }

        }
        System.out.println("total number of solutions iterated: "+count);
    }

    // given a formula that is a conjunction of unary formulae and a translation, obtains an IntSet
    // representing the literals (as integers) that must all be true for the formula to hold
    // private IntSet conjunctionToLiteralSet(Formula conjF, Translation.Whole translation) {

    // }
}
