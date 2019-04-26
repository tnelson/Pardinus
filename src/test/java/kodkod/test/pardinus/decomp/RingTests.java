package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.DecomposedPardinusSolver;
import kodkod.engine.ExtendedSolver;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.RingP;
import kodkod.examples.pardinus.decomp.RingP.Variant1;
import kodkod.examples.pardinus.decomp.RingP.Variant2;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.util.ints.IntSet;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.rules.Timeout;
import org.junit.runners.model.TestTimedOutException;

public class RingTests {
	PardinusSolver psolver;
	
	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);
	@Rule
    public final ExpectedException thrown = ExpectedException.none();

	@Before 
	public void method() throws InterruptedException {
		
		ExtendedOptions opt = new ExtendedOptions();

		opt.setRunDecomposed(true);
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setThreads(4);
		
		Reporter rep = new AbstractReporter() {
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				System.out.println("to bool: " + formula.toString() + ", "
						+ bounds);
			}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				System.out.println("symmetry: " + parts.toString());
			}

			@Override
			public void debug(String debug) {
				System.out.println(debug);				
			}
		};
		opt.setReporter(rep);
		psolver = new PardinusSolver(opt);
	}
	
	@Test 
	public void testSAT9() throws InterruptedException {
		thrown.expect(TestTimedOutException.class);
		int n = 9;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() >= 200);
	}
	
	@Test 
	public void testSAT6() throws InterruptedException {
		thrown.expect(TestTimedOutException.class);
		int n = 6;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() >= 200);
}
	

	@Test 
	public void testUNSAT3a() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT3b() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 8, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT4a() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testUNSAT4b() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertEquals(model.shortName()+": #Runs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns());
		assertEquals(model.shortName()+": #Configs", 24, ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs());
	}
	
	@Test 
	public void testHSAT9() throws InterruptedException {
		int n = 9;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 415);
//		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 415);
//		assertEquals(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT6() throws InterruptedException {
		int n = 6;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertTrue(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() < 415);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 415);
		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
	}
	

	@Test 
	public void testHUNSAT3a() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 9);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 8);
	}
	
	@Test 
	public void testHUNSAT3b() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 9);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 8);
	}
	
	@Test 
	public void testHUNSAT4a() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 25);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 24);
	}
	
	@Test 
	public void testHUNSAT4b() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		psolver.options().setBitwidth(model.getBitwidth());

		final PardinusBounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new PardinusBounds(b1, b2));
		assertFalse(model.shortName()+": SAT", solution.sat());
//		assertTrue(model.shortName()+": Amalg", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.isAmalgamated());
		assertTrue(model.shortName()+": #Runs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumRuns() <= 25);
		assertTrue(model.shortName()+": #Configs", ((DecomposedPardinusSolver<ExtendedSolver>) psolver.solver).executor().monitor.getNumConfigs() <= 24);
	}
	
}
