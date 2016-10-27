package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.DecomposedKodkodSolver;
import kodkod.engine.Solution;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.BoundedExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.RedBlackTreeP;
import kodkod.examples.pardinus.decomp.RedBlackTreeP.Variant1;
import kodkod.examples.pardinus.decomp.RedBlackTreeP.Variant2;
import kodkod.instance.Bounds;
import kodkod.instance.DecompBounds;
import kodkod.util.ints.IntSet;

import org.junit.Before;
import org.junit.Test;

public class RedBlackTests {
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
		opt2.setTargetMode(TMode.DEFAULT);
		opt2.setSolver(SATFactory.PMaxSAT4J);
		opt.setConfigOptions(opt2);
		Reporter rep = new Reporter() {
			@Override
			public void translatingToCNF(BooleanFormula circuit) {
			}
			
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				System.out.println("to bool: " + formula.toString() + ", "
						+ bounds);
			}
			
			@Override
			public void solvingCNF(int primaryVars, int vars, int clauses) {
			}
			
			@Override
			public void skolemizing(Decl decl, Relation skolem,
					List<Decl> context) {
			}
			
			@Override
			public void optimizingBoundsAndFormula() {
			}
			
			@Override
			public void generatingSBP() {
			}
			
			@Override
			public void detectingSymmetries(Bounds bounds) {
			}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				System.out.println("symmetry: " + parts.toString());
			}
			
			@Override
			public void solvingConfig(Solution solution) {
				System.out.println(solution.outcome()+": "
						+ solution.instance().relationTuples().toString());
			}
			
			@Override
			public void configOutcome(Solution solution) {
				System.out.println("dproblem: "+solution.outcome());
			}
			
			@Override
			public void amalgOutcome(Solution solution) {
				System.out.println("amalg: "+solution.outcome());
			}
		};
		opt.setReporter(rep);
		opt2.setReporter(rep);
		psolver = new DecomposedKodkodSolver(opt);
		
		
	}
	
	@Test 
	public void testSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth()+2);
		opt2.setBitwidth(model.getBitwidth()+2);
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
		System.out.println(solution.instance());
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertEquals(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns(), 132);
		assertEquals(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs(), 132);
	}
	
	@Test 
	public void testHSAT3() throws InterruptedException {
		int n = 3;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
		assertEquals(model.shortName()+": SAT", solution.sat(), true);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 5);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 6);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.COUNTER;
		Variant2 v2 = Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 5);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() <= 6);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
	
	@Test 
	public void testHUNSAT4() throws InterruptedException {
		int n = 4;
		Variant1 v1 = Variant1.THEOREM;
		Variant2 v2 = Variant2.V1;
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
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
		psolver.options().setDecomposedMode(DMode.HYBRID);
	
		String[] args = new String[]{n+"",v1.name(),v2.name()};
		DModel model = new RedBlackTreeP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());
		
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();
		
		Solution solution = psolver.solve(f1.and(f2), new DecompBounds(b1, b2));
		assertEquals(model.shortName()+": SAT", solution.sat(), false);
		assertTrue(model.shortName()+": #Configs", psolver.executor().monitor.getNumConfigs() <= 132);
		assertTrue(model.shortName()+": #Runs", psolver.executor().monitor.getNumRuns() < 132);
		assertEquals(model.shortName()+": Amalg", psolver.executor().monitor.isAmalgamated(), true);
	}
}
