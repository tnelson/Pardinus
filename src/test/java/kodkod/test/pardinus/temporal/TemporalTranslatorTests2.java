package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

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

public class TemporalTranslatorTests2 {

	private static Relation A = Relation.unary("A");
	private static Relation Af = Relation.unary("Af");
	private static Relation Al = Relation.unary("Al");
	private static Relation An = Relation.binary("An");
	private static VarRelation S = VarRelation.unary("S");

	PardinusBounds b;
	int n ;
	
	public TemporalTranslatorTests2() {
	
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
		Formula f1 = (S.eq(Af.join(An))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An))).next().next().next().next();
		Formula go = ((S.eq(Af.join(An))).and((S.eq(Af.join(An).join(An).join(An))).previous())).eventually();
		Formula ff = TemporalTranslator.translate(f.and(f0).and(f1).and(f2).and(f3).and(f4).and(go));
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		return;
	}
	
	@Test
	public final void test1() {
		n = 4;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 1);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An))).next().next().next().next();
		Formula go = ((S.eq(Af.join(An))).and((S.eq(Af.join(An).join(An).join(An))).previous())).eventually();
		Formula ff = TemporalTranslator.translate(f.and(f0).and(f1).and(f2).and(f3).and(f4).and(go));
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		return;
	}
	
	@Test
	public final void test2() {
		n = 6;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 3);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An).join(An).join(An).join(An))).next().next().next().next();
		Formula f5 = (S.eq(Af.join(An).join(An).join(An).join(An).join(An))).next().next().next().next().next();
		Formula f6 = (S.eq(Af.join(An).join(An))).next().next().next().next().next().next();
		Formula go = ((S.eq(Af.join(An).join(An).join(An))).and(
				(S.eq(Af.join(An).join(An).join(An).join(An)).and(S.eq(Af.join(An).join(An).join(An).join(An).join(An)).once())).once()
				)).eventually();
		Formula ff = TemporalTranslator.translate(Formula.compose(FormulaOperator.AND, f, f0, f1, f2, f3, f4, f5, f6, go));
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertTrue(sol.sat());
		return;
	}

	@Test
	public final void test3() {
		n = 6;
		doBounds();
		Bounds bb = TemporalTranslator.translate(b, n, 2);
		Formula f = An.totalOrder(A, Af, Al);
		Formula f0 = S.eq(Af);
		Formula f1 = (S.eq(Af.join(An))).next();
		Formula f2 = (S.eq(Af.join(An).join(An))).next().next();
		Formula f3 = (S.eq(Af.join(An).join(An).join(An))).next().next().next();
		Formula f4 = (S.eq(Af.join(An).join(An).join(An).join(An))).next().next().next().next();
		Formula f5 = (S.eq(Af.join(An).join(An).join(An).join(An).join(An))).next().next().next().next().next();
		Formula f6 = (S.eq(Af.join(An).join(An))).next().next().next().next().next().next();
		Formula go = ((S.eq(Af.join(An).join(An).join(An))).and(
				(S.eq(Af.join(An).join(An).join(An).join(An)).and(S.eq(Af.join(An).join(An).join(An).join(An).join(An)).once())).once()
				)).eventually();
		Formula ff = TemporalTranslator.translate(Formula.compose(FormulaOperator.AND, f, f0, f1, f2, f3, f4, f5, f6, go));
		
		ExtendedOptions options = new ExtendedOptions();
		Solver solver = new Solver(options);
		Solution sol = solver.solve(ff, bb);
		System.out.println(sol.toString());
		assertFalse(sol.sat());
		return;
	}
}
