/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.test.pardinus.decomp;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Iterator;

import org.junit.BeforeClass;
import org.junit.Test;

/**
 * Basic tests to check whether the temporal bounded engine is running.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 */
public class BaseTests {
	private static PardinusSolver dsolver;
	private static ExtendedOptions opt;

	@BeforeClass
	public static void method() throws InterruptedException {
		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setRunDecomposed(true);
		opt.setRunTemporal(false);
//		Reporter rep = new SLF4JReporter();
//		opt.setReporter(rep);
//		opt.configOptions().setReporter(rep);
	}

	@Test
	public void testSAT() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds2.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.eq(c).not()); // never trivial
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol;
		for (int i = 0; i < 13; i++) {
			sol = sols.next();
//			System.out.println("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialConfig() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.in(b).and(b.eq(c).not()); // config trivial
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol;
		for (int i = 0; i < 15; i++) {
			sol = sols.next();
//			System.out.println("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialRem() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)); // all remainder trivial
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol;
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < 18; i++) {
			sol = sols.next();
			sb.append("** "+sol.instance().relationTuples().toString()+"\n");
			assertTrue("base problem should be sat", sol.sat());
		}
//		System.out.println(sb.toString());
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSATTrivialSomeRem() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds2.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.in(c)); // some remainder trivial
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol;
		for (int i = 0; i < 9; i++) {
			sol = sols.next();
//			System.out.println("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	@Test
	public void testSAT2() {
		opt.setSolver(SATFactory.MiniSat);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).not().and(a.in(b)).and(b.eq(c).not()); // never trivial
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		Solution sol;
		for (int i = 0; i < 13; i++) {
			sol = sols.next();
//			System.out.println("** "+sol.instance().toString());
			assertTrue("base problem should be sat", sol.sat());
		}
		sol = sols.next();
		assertFalse("base problem should have 9 sols", sol.sat());
	}
	
	
	/*
	@Test
	public void testSATLen() {
		opt.setSolver(SATFactory.DefaultSAT4J);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setMinTraceLength(10);
		opt.setMaxTraceLength(20);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testUNSATLen() {
		opt.setSolver(SATFactory.DefaultSAT4J);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setMaxTraceLength(1);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should not be sat for this trace length", sol.sat());
	}
	
	@Test
	public void testUNSAT() {
		opt.setSolver(SATFactory.DefaultSAT4J);
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
		Formula run = r.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should be unsat",sol.sat());
	}
	
	@Test
	public void testSATU() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunUnbounded(true);
		opt.setRunTemporal(true);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.lone()).always();
		Formula run = a.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertTrue("base problem should be sat", sol.sat());
	}
	
	@Test
	public void testUNSATU() {
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		opt.setRunUnbounded(true);
		opt.setRunTemporal(true);
		dsolver = new PardinusSolver(opt);

		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");
		Relation r = Relation.binary_variable("r");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		bounds.bound(r, a.product(b));
		Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
		Formula run = r.no().eventually();
		
		Solution sol = dsolver.solveAll(formula.and(run), bounds).next();
		
		assertFalse("base problem should be unsat",sol.sat());
	}
	
	@Test
	public void testInvalid1() {
		try {
			opt.setSolver(SATFactory.DefaultSAT4J);
			opt.setRunTemporal(false);
			opt.setRunUnbounded(false);
			dsolver = new PardinusSolver(opt);
			int n = 2;

			Relation a = Relation.unary_variable("a");
			Relation b = Relation.unary("b");
			Relation r = Relation.binary_variable("r");

			Object[] atoms = new Object[n * 2];
			for (int i = 0; i < n; i++)
				atoms[i] = "A" + i;
			for (int i = 0; i < n; i++)
				atoms[n + i] = "B" + i;

			Universe uni = new Universe(atoms);
			TupleFactory f = uni.factory();
			TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
			TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

			PardinusBounds bounds = new PardinusBounds(uni);
			bounds.bound(a, as);
			bounds.bound(b, bs);
			bounds.bound(r, a.product(b));
			Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
			Formula run = r.no().eventually();
			
			dsolver.solveAll(formula.and(run), bounds).next();
			fail("must run temporal for temporal problems");
		} catch (AssertionError e) {}
	}
	
	@Test
	public void testInvalid5() {
		try {
			opt.setSolver(SATFactory.DefaultSAT4J);
			opt.setRunTemporal(false);
			opt.setRunUnbounded(false);
			opt.setMaxTraceLength(0);
			dsolver = new PardinusSolver(opt);
			int n = 2;

			Relation a = Relation.unary_variable("a");
			Relation b = Relation.unary("b");
			Relation r = Relation.binary_variable("r");

			Object[] atoms = new Object[n * 2];
			for (int i = 0; i < n; i++)
				atoms[i] = "A" + i;
			for (int i = 0; i < n; i++)
				atoms[n + i] = "B" + i;

			Universe uni = new Universe(atoms);
			TupleFactory f = uni.factory();
			TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
			TupleSet bs = f.range(f.tuple("B0"), f.tuple("B" + (n - 1)));

			PardinusBounds bounds = new PardinusBounds(uni);
			bounds.bound(a, as);
			bounds.bound(b, bs);
			bounds.bound(r, a.product(b));
			Formula formula = ((a.eq(a.prime()).not())).and(r.some()).always();
			Formula run = r.no().eventually();
			
			dsolver.solveAll(formula.and(run), bounds).next();
			fail("must run temporal for temporal problems");
		} catch (AssertionError e) {}
	}


	@Test
	public void testInvalid2() {
		try {
			opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
			opt.setRunTemporal(false);
			opt.setRunUnbounded(true);
			dsolver = new PardinusSolver(opt);
			fail("must run temporal for unbounded run");
		} catch (Exception e) {}
	}

	@Test
	public void testInvalid3() {
		try {
			opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
			opt.setRunTemporal(true);
			opt.setRunUnbounded(false);
			dsolver = new PardinusSolver(opt);
			fail("must select bounded solver for bounded run");
		} catch (AssertionError e) {}
	}

	@Test
	public void testInvalid4() {
		try {
			opt.setSolver(SATFactory.DefaultSAT4J);
			opt.setRunTemporal(true);
			opt.setRunUnbounded(true);
			dsolver = new PardinusSolver(opt);
			fail("must select unbounded solver for unbounded run");
		} catch (AssertionError e) {}
	}
	*/
}
