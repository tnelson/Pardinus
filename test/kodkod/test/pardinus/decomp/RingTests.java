package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.RingP;
import kodkod.examples.pardinus.decomp.RingP.Variant1;
import kodkod.examples.pardinus.decomp.RingP.Variant2;
import kodkod.instance.Bounds;
import kodkod.pardinus.decomp.DModel;
import kodkod.pardinus.decomp.DOptions.Modes;
import kodkod.pardinus.decomp.DSolver;

import org.junit.Before;
import org.junit.Test;

public class RingTests {
	Solver solver;
	DSolver psolver;
	
	@Before 
	public void method() throws InterruptedException {
		
		solver = new Solver();
		psolver = new DSolver(solver);

		solver.options().setSymmetryBreaking(20);
		solver.options().setSolver(SATFactory.Glucose);
		psolver.options().setMode(Modes.PARALLEL);
		psolver.options().setThreads(4);
		
	}
	
	@Test 
	public void testSAT9() throws InterruptedException {
		int n = 9;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() >= 200);
	}
	
	@Test 
	public void testSAT6() throws InterruptedException {
		int n = 6;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() >= 200);
}
	

	@Test 
	public void testUNSAT3a() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 8);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 8);
	}
	
	@Test 
	public void testUNSAT3b() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 8);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 8);
	}
	
	@Test 
	public void testUNSAT4a() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 24);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 24);
	}
	
	@Test 
	public void testUNSAT4b() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 24);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 24);
	}
	
	@Test 
	public void testHSAT9() throws InterruptedException {
		int n = 9;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
//		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 415);
//		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 415);
//		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT6() throws InterruptedException {
		int n = 6;
		int t = 20;
		Variant1 v1 = Variant1.BADLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 415);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 415);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
}
	

	@Test 
	public void testHUNSAT3a() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 8);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 8);	}
	
	@Test 
	public void testHUNSAT3b() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 8);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 8);	}
	
	@Test 
	public void testHUNSAT4a() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODLIVENESS;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 24);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 24);	}
	
	@Test 
	public void testHUNSAT4b() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant1 v1 = Variant1.GOODSAFETY;
		Variant2 v2 = Variant2.VARIABLE;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",t+"",v1.name(),v2.name()};
		DModel model = new RingP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 24);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 24);
	}
	


}
