package kodkod.test.unit.proofExplanation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

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
    private Formula f;
    private final PardinusBounds pbounds;

    public ReducedResolutionTraceTest() {
        List<String> atoms = new ArrayList<String>(NATOMS);
		for (int i = 0; i < NATOMS; i++) {
			atoms.add(""+i);
		}
        final Universe universe = new Universe(atoms);
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

    // {1, 2}, {1, -2}, {-1, 2}, {-1, -2}
    @Before
    public void setUpSimplest() throws Exception {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some());
        this.f.and(p.some().or(q.no()));
        this.f.and(p.no().or(q.some()));
        this.f.and(p.no().or(q.no()));

        
    }

    // {1, 2, -3}, {3}, {1, -2}, {-1, 2}, {-1, -2}
    @Before
    public void setUpWithThree() throws Exception {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some());
        this.f.and(p.some().or(q.no()));
        this.f.and(q.no().or(r.some()));
        this.f.and(p.no().or(r.no()));
        this.f.and(q.some().or(r.no()));
        this.f.and(q.some().or(p.no()));
        this.f.and(q.no().or(r.no()));
    }

    // {-1, -2, 3}, {-3}, {-1, 2}, {1, -2}, {1, 2}
    @Before
    public void setUpWithThreeNegation() throws Exception {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.no().or(q.no());
        this.f.and(p.no().or(q.some()));
        this.f.and(q.some().or(r.no()));
        this.f.and(p.some().or(r.some()));
        this.f.and(q.no().or(r.some()));
        this.f.and(q.no().or(p.some()));
        this.f.and(q.some().or(r.some()));
    }

    // {1, 2, -4}, {3, 4, -5}, {5}, {1, 2, -3}, {-1, 2, -3}, {-1, 2, 3},
    // {1, -2, 3}, {1, -2, -3}, {-1, -2, 3}, {-1, -2, -3}
    @Before
    public void setUpFiveLiterals() throws Exception {
        this.pbounds.bound(p, this.factory.allOf(1));
        this.pbounds.bound(q, this.factory.allOf(1));
        this.pbounds.bound(r, this.factory.allOf(1));

        this.f = p.some().or(q.some()).or(r.some());
        this.f.and(p.some().or(q.no()).or(r.no()));
        this.f.and(p.no().or(q.some()).or(r.no()));
        this.f.and(p.no().or(q.no()).or(r.no()));
        this.f.and(p.some().or(q.no()).or(r.some()));
        this.f.and(p.some().or(q.no()).or(r.some()));
        this.f.and(p.some().or(q.some()).or(r.no()));
        this.f.and(p.no().or(q.no()).or(r.some()));
    }

    // testing the behavior of the `core` method

    

}
