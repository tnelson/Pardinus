package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.Iterator;
import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

// TODO: test trivials
// TODO: test symbolic
// TODO: test decomposed

public class TemporalIterationTests {

	@Test
	public void test() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		
		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		Formula formula = a.one().always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(10, c);
		solver.free();

	}
	
	@Test
	public void testLower() {
		final int n = 3;

		Relation a = Relation.unary_variable("a");
		
		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ls = f.setOf(f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, ls, as);
		Formula formula = a.some().always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(96, c);
		solver.free();

	}
	
	@Test
	public void testPast() {
		final int n = 1;

		Relation a = Relation.unary_variable("a");
		
		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		Formula formula = a.some().previous().once().eventually().and(a.no());

		ExtendedOptions opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(9, c);
		solver.free();

	}
	
	@Test
	public void testLowerUbd() {
		final int n = 2;

		Relation a = Relation.unary_variable("a");
		
		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ls = f.setOf(f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, ls, as);
		Formula formula = a.some().always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setReporter(new SLF4JReporter());
		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(5);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		
		while (sols.hasNext() && c < 10) {
					
			Solution sol = sols.next();
			c++;

			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(10, c);
		solver.free();

	}
	

	@Test
	public void testTempSkolem() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ls = f.setOf(f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, ls, as);
		bounds.boundExactly(b, as);
		Formula formula = a.eq(b).always().eventually();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(5, c);
		solver.free();
	}
	
	@Test
	public void testSkolem() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.boundExactly(a, as);
		bounds.bound(b, as);
		Variable v = Variable.unary("x");
		Formula formula = v.in(a).forSome(v.oneOf(b)).always().and(b.one().next());

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSkolemDepth(1);
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(6, c);
		solver.free();
	}
	
	@Test
	public void testSkolem2() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, as);
		Variable v = Variable.unary("x");
		Formula formula = a.some().always().and(v.in(b).forSome(v.oneOf(b)));

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSkolemDepth(1);
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(24, c);
		solver.free();
	}
	
	
	@Test
	public void testSkolemUnd() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, as);
		Variable v = Variable.unary("x");
		Formula formula = v.in(a).forSome(v.oneOf(b)).always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
		opt.setRunUnbounded(true);
		opt.setSkolemDepth(1);
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		
		while (sols.hasNext() && c < 5) {
					
			Solution sol = sols.next();
			c++;

			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(5, c);
		solver.free();
	}

	@Test
	public void testNoRef() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ls = f.setOf(f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, ls, as);
		Formula formula = a.some().always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(2);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(9, c);
		solver.free();
	}
	
	
	@Test
	public void testTempSkolemUbd() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet ls = f.setOf(f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, ls, as);
		bounds.boundExactly(b, as);
		Formula formula = a.eq(b).always().eventually();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
		opt.setRunUnbounded(true);
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		
		while (sols.hasNext() && c < 10) {
					
			Solution sol = sols.next();
			c++;

			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(10, c);
		solver.free();
	}
	
	@Test
	public void testTempSkolemTotalOrder() {
		int n = 2;

		Relation a = Relation.unary("a");
		Relation af = Relation.unary("first");
		Relation al = Relation.unary("last");
		Relation an = Relation.binary("next");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(an, as.product(as));
		bounds.bound(af, as);
		bounds.bound(al, as);
		bounds.boundExactly(b, as);
		Formula formula = b.in(a).always().eventually().and(an.totalOrder(a, af, al));

		ExtendedOptions opt = new ExtendedOptions();
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		while (sols.hasNext()) {
					
			Solution sol = sols.next();
			c++;
			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		assertEquals(2, c);
		solver.free();

	}
	
	@Test
	public void testTempSkolemTotalOrderUbd() {
		int n = 2;

		Relation a = Relation.unary("a");
		Relation af = Relation.unary("first");
		Relation al = Relation.unary("last");
		Relation an = Relation.binary("nextt");
		Relation b = Relation.unary_variable("b");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(an, as.product(as));
		bounds.bound(af, as);
		bounds.bound(al, as);
		bounds.boundExactly(b, as);
		Formula formula = b.in(a).always().eventually().and(an.totalOrder(a, af, al));

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
		opt.setRunUnbounded(true);
		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(3);
		PardinusSolver solver = new PardinusSolver(opt);
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);

		int c = 0;
		
		while (sols.hasNext() && c < 10) {
					
			Solution sol = sols.next();
			c++;

			if (sol.sat())
				System.out.println(sol.instance().toString());
		}
		
		assertEquals(2, c);
		solver.free();

	}
	
	@Test
	public void election() {
		int n = 3;

		Relation id 		= Relation.unary("Id");
		Relation next 		= Relation.binary("next");
		Relation process 	= Relation.unary("Process");
		Relation idf	 	= Relation.binary("id");
		Relation succ 		= Relation.binary("succ");
		Relation outbox 	= Relation.binary_variable("outbox");
		Relation elected 	= Relation.unary_variable("Elected");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i++)
			atoms[i] = "I"+i;
		for (int i = 0; i < n; i++)
			atoms[n+i] = "P"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet is = f.range(f.tuple("I0"), f.tuple("I"+(n-1)));
		TupleSet ps = f.range(f.tuple("P0"), f.tuple("P"+(n-1)));
		TupleSet ns = f.noneOf(2);
		for (int i = 0; i < n-1; i++) {
			ns.add(f.tuple("I"+i,"I"+(i+1)));
		}

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.boundExactly(id,is);
		bounds.boundExactly(next, ns);
		bounds.bound(process,ps);
		bounds.bound(idf, process.product(id));
		bounds.bound(succ, process.product(process));
		bounds.bound(outbox, process.product(id));
		bounds.bound(elected, process);

		Variable p1 = Variable.unary("p");
		Formula f1 = p1.join(idf).one().forAll(p1.oneOf(process));
		Variable i = Variable.unary("i");
		Formula f2 = idf.join(i).lone().forAll(i.oneOf(id));
		Variable p3 = Variable.unary("p");
		Formula f3 = p3.join(succ).one().forAll(p3.oneOf(process));
		Variable p4 = Variable.unary("p");
		Formula f4 = process.in(p4.join(succ.closure())).forAll(p4.oneOf(process));
		
		Formula f5 = outbox.eq(idf);
		Variable p6 = Variable.unary("p"), i6 = Variable.unary("i");
		Expression e6a = outbox.difference(p6.product(i6));
		Expression e6b = p6.join(succ).product(i6.difference(next.closure().join(p6.join(succ.join(idf)))));
		Formula f6a = outbox.prime().eq((e6a).union(e6b));
		Formula f6 = f6a.forSome(p6.oneOf(process).and(i6.oneOf(p6.join(outbox)))).always();
		Variable p7 = Variable.unary("p");
		Formula f7a = (p7.join(idf).in(p7.join(outbox)).and(p7.join(idf).in(p7.join(outbox)).not().previous())).once();
		Formula f7 = elected.eq(f7a.comprehension(p7.oneOf(process))).always();
		
//		Formula f8 = idf.in(process.product(id));
//		Formula f9 = succ.in(process.product(process));
//		Formula f10 = outbox.in(process.product(id)).always();
//		Formula f11 = elected.in(process).always();

		ExtendedOptions opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(8);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Formula formula = NaryFormula.and(f1,f2,f3,f4,f5,f6,f7,elected.some().eventually());
		
		assertTrue(solver.solve(formula, bounds).sat());

		Iterator<Solution> sols = solver.solveAll(formula, bounds);
		
		System.out.println(bounds);
		System.out.println(formula);
		
		for (int j = 0;j<10 && sols.hasNext();j++) {
			Solution sol = sols.next();
	
			if (sol.sat()) {
				System.out.println(sol.instance().toString());
			
//				Set<TemporalInstance> instns = ((TemporalInstance) sol.instance()).unrollStep(5);
				
//				for (TemporalInstance k : instns)
//					System.out.println(k.toString());
			}

		}
		solver.free();

	}
	
}