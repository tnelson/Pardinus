package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Universe;

public class PastTests {

	private static Relation A = Relation.unary("A");
	private static Relation Af = Relation.unary("Af");
	private static Relation Al = Relation.unary("Al");
	private static Relation An = Relation.binary("An");
	private static VarRelation S = VarRelation.unary("S");

	PardinusBounds b;
	int n ;
	
	public PastTests() {
	
	}
	
	void doBounds() {
		List<Object> atoms = new ArrayList<Object>();
		for (int i = 0; i < n; i++)
			atoms.add("A"+i);
		Universe u = new Universe(atoms);
		b = new PardinusBounds(u);
		b.bound(An, u.factory().allOf(1).product(u.factory().allOf(1)));
		b.bound(A, u.factory().allOf(1));
		b.bound(Af, u.factory().allOf(1));
		b.bound(Al, u.factory().allOf(1));
		b.bound(S, u.factory().allOf(1));
	}
	
	@Test
	public final void test() {
		n = 4;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).in(S))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = ((Af.join(An).in(S))).next().next().next().next();
		Formula go = (((Af.join(An).in(S))).and((S.eq(Af.join(An).join(An).join(An))).previous())).eventually();
		Formula tt = f.and(f0).and(f1).and(f2).and(f3).and(f4).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void test1() {
		n = 4;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 1);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).in(S))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = ((Af.join(An).in(S))).next().next().next().next();
		Formula go = (((Af.join(An).in(S))).and((S.eq(Af.join(An).join(An).join(An))).previous())).eventually();
		Formula tt = f.and(f0).and(f1).and(f2).and(f3).and(f4).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void test2() {
		n = 6;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 3);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).in(S))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An).join(An).join(An).join(An))).next().next().next().next();
		Formula f5 = (S.eq(Af.join(An).join(An).join(An).join(An).join(An))).next().next().next().next().next();
		Formula f6 = (S.eq(Af.join(An).join(An))).next().next().next().next().next().next();
		Formula go = ((S.eq(Af.join(An).join(An).join(An))).and(
				(S.eq(Af.join(An).join(An).join(An).join(An)).and(S.eq(Af.join(An).join(An).join(An).join(An).join(An)).once())).once()
				)).eventually();
		Formula tt = Formula.compose(FormulaOperator.AND, f, f0, f1, f2, f3, f4, f5, f6, go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(3, TemporalTranslator.countHeight(tt));
		return;
	}

	@Test
	public final void test3() {
		n = 6;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).in(S))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An).join(An).join(An).join(An))).next().next().next().next();
		Formula f5 = (S.eq(Af.join(An).join(An).join(An).join(An).join(An))).next().next().next().next().next();
		Formula f6 = (S.eq(Af.join(An).join(An))).next().next().next().next().next().next();
		Formula go = ((S.eq(Af.join(An).join(An).join(An))).and(
				(S.eq(Af.join(An).join(An).join(An).join(An)).and(S.eq(Af.join(An).join(An).join(An).join(An).join(An)).once())).once()
				)).eventually();
		Formula tt = Formula.compose(FormulaOperator.AND, f, f0, f1, f2, f3, f4, f5, f6, go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(3, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB1() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB2() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB3() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB4() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).always().next();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).eventually();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB5() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testB6() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = ((Af.join(An).eq(S))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always().next().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testC1() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An).union(Af))).always().next();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testC2() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testC3() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testC4() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).eventually();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD1() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).always().next();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD2() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).next().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD3() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD4() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).and((Af.in(S)).previous())).eventually();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD5() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
	
	@Test
	public final void testD6() {
		n = 2;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Expression.NONE);
		Formula f1 = (S.eq(Af.join(An).union(Af))).next().always();
		Formula go = (((Af.join(An).in(S))).implies((Af.in(S)).previous())).always().next().next();
		Formula tt = f.and(f0).and(f1).and(go);
		Formula ff = TemporalTranslator.translate(tt,n);
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		assertEquals(2, TemporalTranslator.countHeight(tt));
		return;
	}
}
