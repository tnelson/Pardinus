package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import kodkod.ast.Formula;
import kodkod.engine.DecomposedKodkodSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.BoundedExtendedOptions;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.HotelP;
import kodkod.examples.pardinus.decomp.HotelP.Variant;
import kodkod.instance.Bounds;

import org.junit.Before;
import org.junit.Test;

public class HotelTests {
	DecomposedKodkodSolver psolver;
	BoundedExtendedOptions opt, opt2;
	
	@Before 
	public void method() throws InterruptedException {

		opt = new BoundedExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.PARALLEL);
		opt.setThreads(4);
		opt2 = new BoundedExtendedOptions(opt);
		opt2.setRunTarget(false);
		opt2.setReporter(new ConsoleReporter());

//		opt2.setTargetMode(TMode.FAR);
//		opt2.setSolver(SATFactory.PMaxSAT4J);
		opt.setConfigOptions(opt2);
		opt.setReporter(new ConsoleReporter());
		psolver = new DecomposedKodkodSolver(opt);
		
	}
	
	@Test 
	public void testSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 20);

	}
	
	@Test 
	public void testSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 75);

	}
	
	@Test 
	public void testSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() >= 200);

	}
	
	@Test 
	public void testUNSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 20);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 20);
	}
	
	@Test 
	public void testUNSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 75);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 75);
	}
	
	@Test 
	public void testUNSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 312);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 312);
	}
	
	@Test 
	public void testHSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 20);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 20);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), false);
	}
	
	@Test 
	public void testHSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 75);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 75);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), false);
	}
	
	@Test 
	public void testHSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 312);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 312);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), false);
	}
	
	@Test 
	public void testHUNSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 20);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 20);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 75);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 75);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		psolver.options().setDecomposedMode(DMode.HYBRID);

		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 312);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 312);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}

}
