package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.RedBlackTreeP;
import kodkod.examples.pardinus.decomp.RedBlackTreeP.Variant1;
import kodkod.examples.pardinus.decomp.RedBlackTreeP.Variant2;
import kodkod.instance.Bounds;
import kodkod.pardinus.decomp.DModel;
import kodkod.pardinus.decomp.DOptions.Modes;
import kodkod.pardinus.decomp.DSolver;

import org.junit.Before;
import org.junit.Test;

public class RedBlackTests {
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
	public void testSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 5);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 5);
	}
	
	@Test 
	public void testSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 14);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 14);
	}
	
	@Test 
	public void testSAT5() throws InterruptedException {
		int n = 5;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 42);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 42);
	}
	
	@Test 
	public void testSAT6() throws InterruptedException {
		int n = 6;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 132);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 132);
	}
	
	@Test 
	public void testUNSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 5);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 5);
	}
	
	@Test 
	public void testUNSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 14);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 14);
	}
	
	@Test 
	public void testUNSAT5() throws InterruptedException {
		int n = 5;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 42);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 42);
	}
	
	@Test 
	public void testUNSAT6() throws InterruptedException {
		int n = 6;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 132);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 132);
	}
	
	@Test 
	public void testHSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 5);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 5);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 14);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 14);
//		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT5() throws InterruptedException {
		int n = 5;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 42);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 42);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT6() throws InterruptedException {
		int n = 6;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 132);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 132);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 5);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 5);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 14);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 14);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT5() throws InterruptedException {
		int n = 5;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 42);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 42);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT6() throws InterruptedException {
		int n = 6;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		psolver.options().setMode(Modes.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 132);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 132);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
}
