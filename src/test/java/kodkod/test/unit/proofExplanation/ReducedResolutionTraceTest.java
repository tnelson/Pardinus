package kodkod.test.unit.proofExplanation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.ResolutionBasedProof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.proofExplanation.core.ReducedResolutionTrace;
import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;

/**
 * Tests ReducedResolutionTrace construction and behavior.
 */
public class ReducedResolutionTraceTest {
    private final int NATOMS = 1;
    private final TupleFactory factory;
    private final PardinusSolver solver;
    private final Relation p = Relation.unary("P");
    private final Relation q = Relation.unary("Q");
    private final Relation r = Relation.unary("R");
    private final Universe universe;
    private Formula f;
    private PardinusBounds pbounds;

    public ReducedResolutionTraceTest() {
        List<String> atoms = new ArrayList<String>(NATOMS);
		for (int i = 0; i < NATOMS; i++) {
			atoms.add(""+i);
		}
        this.universe = new Universe(atoms);
        this.factory = universe.factory();

        ExtendedOptions eo = new ExtendedOptions();
        eo.setRunTarget(false);

        // only (?) one that gives cores to Kodkod
        eo.setSolver(SATFactory.MiniSatProver);
        eo.setSymmetryBreaking(0);
        eo.setLogTranslation(2);
        eo.setCoreGranularity(2);
        eo.setBitwidth(1); // minimum allowable

        this.solver = new PardinusSolver(eo);

        this.pbounds = new PardinusBounds(universe);  
        
        // will be changed from this trivial UNSAT during setup
        this.f = p.some().and(p.no());
    }

    // {1, 2, -3}, {1, -2, -4}, {-1, 2, -5}, {-1, -2, -6}, {3}, {4}, {5}, {6}
    @Before
    public void setUpSimplest() {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some());
        this.f = this.f.and(p.some().or(q.no()));
        this.f = this.f.and(p.no().or(q.some()));
        this.f = this.f.and(p.no().or(q.no()));

        //System.out.println("Formula: " + this.f);
    }

    // {1, 2, -4}, {1, -2, -5}, {-2, -3, -6}, {-1, -3, -7}, {2, -3, -8}, {-1, 2, -9}, {-2, -3, -10},
    // {4}, {5}, {6}, {7}, {8}, {9}, {10}
    @Before
    public void setUpWithThree() {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some());
        this.f = this.f.and(p.some().or(q.no()));
        this.f = this.f.and(q.no().or(r.some()));
        this.f = this.f.and(p.no().or(r.no()));
        this.f = this.f.and(q.some().or(r.no()));
        this.f = this.f.and(q.some().or(p.no()));
        this.f = this.f.and(q.no().or(r.no()));

        //System.out.println("Formula: " + this.f);
    }

    // {-1, -2, 3}, {-3}, {-1, 2}, {1, -2}, {1, 2}
    @Before
    public void setUpWithThreeNegation() {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.no().or(q.no());
        this.f = this.f.and(p.no().or(q.some()));
        this.f = this.f.and(q.some().or(r.no()));
        this.f = this.f.and(p.some().or(r.some()));
        this.f = this.f.and(q.no().or(r.some()));
        this.f = this.f.and(q.no().or(p.some()));
        this.f = this.f.and(q.some().or(r.some()));

        //System.out.println("Formula: " + this.f);
    }

    // {1, 2, -4}, {3, 4, -5}, {5}, {1, 2, -3}, {-1, 2, -3}, {-1, 2, 3},
    // {1, -2, 3}, {1, -2, -3}, {-1, -2, 3}, {-1, -2, -3}
    @Before
    public void setUpFiveLiterals() {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some()).or(r.some());
        this.f = this.f.and(p.some().or(q.no()).or(r.no()));
        this.f = this.f.and(p.no().or(q.some()).or(r.no()));
        this.f = this.f.and(p.no().or(q.no()).or(r.no()));
        this.f = this.f.and(p.some().or(q.no()).or(r.some()));
        this.f = this.f.and(p.some().or(q.no()).or(r.some()));
        this.f = this.f.and(p.some().or(q.some()).or(r.no()));
        this.f = this.f.and(p.no().or(q.no()).or(r.some()));

        //System.out.println("Formula: " + this.f);
    }

    @After
    public void tearDown() {
        this.pbounds = new PardinusBounds(this.universe);
        this.f = null;
    }

    // testing the behavior of the `core` method
    @Test
    public void coreOnSimplestExampleNoAssumps() {
        setUpSimplest();
        
        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, new IntTreeSet());
                IntSet reducedCore = reducedTrace.core();
                IntSet origCore = origTrace.core();

                // no assumptions, so origCore and reducedCore are equal
                assertEquals(reducedCore, origCore);
            }
        }

        tearDown();
    }

    @Test
    public void coreOnSimplestExampleOnePosAssump() {
        setUpSimplest();
        
        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                IntSet assumps = new IntTreeSet();
                assumps.add(1);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                IntSet reducedCore = reducedTrace.core();

                IntSet expectedIndices = new IntTreeSet();
                expectedIndices.add(2); // {-1, 2, -5}
                expectedIndices.add(3); // {-1, -2, -6}
                expectedIndices.add(6); // {5}
                expectedIndices.add(7); // {6}

                assertEquals(expectedIndices, reducedCore);
            }
        }

        tearDown();
    }

    @Test
    public void coreOnSimplestExampleAxiomBecomesEmpty() {
        setUpSimplest();
        
        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                IntSet assumps = new IntTreeSet();
                assumps.add(-3);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                IntSet reducedCore = reducedTrace.core();

                IntSet expectedIndices = new IntTreeSet();
                expectedIndices.add(4); // {3}

                assertEquals(expectedIndices, reducedCore);
            }
        }

        tearDown();
    }

    @Test
    public void coreOnSimplestExampleMultipleAssumps() {
        setUpSimplest();

        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                IntSet assumps = new IntTreeSet();
                assumps.add(1);
                assumps.add(2);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                IntSet reducedCore = reducedTrace.core();

                IntSet expectedIndices = new IntTreeSet();
                expectedIndices.add(3); // {-1, -2, -6}
                expectedIndices.add(7); // {6}

                assertEquals(expectedIndices, reducedCore);
            }
        }

        tearDown();
    }

    @Test
    public void coreOnThreeExampleWithResolventContradicted() {
        setUpWithThree();

        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                IntSet assumps = new IntTreeSet();
                assumps.add(3);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                IntSet reducedCore = reducedTrace.core();

                IntSet expectedIndices = new IntTreeSet();
                expectedIndices.add(0); // {1, 2, -4}
                expectedIndices.add(1); // {1, -2, -5}
                expectedIndices.add(3); // {-1, -3, -7}
                expectedIndices.add(7); // {4}
                expectedIndices.add(8); // {5}
                expectedIndices.add(10); // {7}

                assertEquals(expectedIndices, reducedCore);
            }
        }

        tearDown();
    }

    @Test
    public void coreOnThreeExampleWithPosAndNegAssumps() {
        setUpWithThree();

        for (Explorer<Solution> sols = solver.solveAll(f, pbounds); sols.hasNext(); ) {
            Solution sol = sols.next();
            if (sol.unsat()) {
                sol.proof().minimize(new RCEStrategy(sol.proof().log()));
                ResolutionBasedProof ohno = (ResolutionBasedProof) sol.proof();
                ResolutionTrace origTrace = ohno.solver.proof();
                IntSet assumps = new IntTreeSet();
                assumps.add(1);
                assumps.add(-2);
                ReducedResolutionTrace reducedTrace = new ReducedResolutionTrace(origTrace, assumps);
                IntSet reducedCore = reducedTrace.core();

                IntSet expectedIndices = new IntTreeSet();
                expectedIndices.add(5); // {-1, 2, -9}
                expectedIndices.add(12); // {9}

                assertEquals(expectedIndices, reducedCore);
            }
        }

        tearDown();
    }

    // TODO: add more tests

}
