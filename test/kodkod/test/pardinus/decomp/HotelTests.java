package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.HotelP;
import kodkod.examples.pardinus.decomp.HotelP.Variant;
import kodkod.instance.Bounds;
import kodkod.pardinus.decomp.DModel;
import kodkod.pardinus.decomp.DOptions.Modes;
import kodkod.pardinus.decomp.DSolver;

import org.junit.Before;
import org.junit.Test;

public class HotelTests {
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
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), true);
	}
	
	@Test 
	public void testSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), true);
	}
	
	@Test 
	public void testSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.INTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), true);
	}
	
	@Test 
	public void testUNSAT3() throws InterruptedException {
		int n = 3;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), false);
		assertEquals("Hotel "+n+" "+v1.name()+": #Configs", psolver.executor().monitor.solutions().size(), 20);
	}
	
	@Test 
	public void testUNSAT4() throws InterruptedException {
		int n = 4;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), false);
		assertEquals("Hotel "+n+" "+v1.name()+": #Configs", psolver.executor().monitor.solutions().size(), 75);
	}
	
	@Test 
	public void testUNSAT5() throws InterruptedException {
		int n = 5;
		int t = 20;
		Variant v1 = Variant.NOINTERVENES;
		
		String[] args = new String[]{n+"",t+"",v1.name()};
		DModel model = new HotelP(args);

		solver.options().setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1, f2, b1, b2);
		assertEquals("Hotel "+n+" "+t+" "+v1.name()+": SAT", solution.sat(), false);
		assertEquals("Hotel "+n+" "+v1.name()+": #Configs", psolver.executor().monitor.solutions().size(), 312);
	}

}
