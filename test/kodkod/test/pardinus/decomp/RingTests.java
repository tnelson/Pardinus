package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), true);
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), true);
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), false);
		assertEquals("Ring "+n+" "+v1.name()+" "+v2.name()+": #Configs", psolver.executor().monitor.solutions().size(), 8);
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), false);
		assertEquals("Ring "+n+" "+v1.name()+" "+v2.name()+": #Configs", psolver.executor().monitor.solutions().size(), 8);
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), false);
		assertEquals("Ring "+n+" "+v1.name()+" "+v2.name()+": #Configs", psolver.executor().monitor.solutions().size(), 24);
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
		assertEquals("Ring "+n+" "+t+" "+v1.name()+" "+v2.name()+": SAT", solution.sat(), false);
		assertEquals("Ring "+n+" "+v1.name()+" "+v2.name()+": #Configs", psolver.executor().monitor.solutions().size(), 24);
	}
	


}
