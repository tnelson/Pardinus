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

package kodkod.test.pardinus.temporal;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.SymmetryP;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import java.util.Collections;
import java.util.HashSet;

import org.junit.Test;

/**
 * Tests whether the symmetries are being correctly calculated for decomposed
 * problems by comparing with the amalgamated problem, as well as whether every
 * solution is being enumerated. Also tests problems where either the partial or
 * integrated problem become trivial. Uses the models from {@link SymmetryP}.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
public class ExplorationTests {

	@Test
	public void testBasic() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		
		// needs to expand by 1
		Formula ext = a.eq(a.prime()).not();
		System.out.println("Extending with "+ext);
//		sol = sols.branch(4,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		// needs to expand by 3
		ext = b.eq(b.prime()).not();
		System.out.println("Extending with "+ext);
//		sol = sols.branch(5,ext);
		System.out.println(sol.instance());
		assertEquals(8, ((TemporalInstance) sol.instance()).prefixLength());

		// reduces but must then expand by 3
		ext = b.eq(b.prime());
		System.out.println("Extending with "+ext);
//		sol = sols.branch(1,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		// conflict with original formula
		ext = a.eq(a.prime());
		System.out.println("Extending with "+ext);
//		sol = sols.branch(4,ext);
		System.out.println(sol.instance());
		assertFalse(sol.sat());

		solver.free();
	}
	
	@Test
	public void testBasic2() {
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
		Formula formula = ((a.eq(a.prime()).not()).and(a.intersection(b).no())).always().and(b.some()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		sol = sols.next();
		System.out.println(sol.instance());
		
		// needs to expand by 1
		Formula ext = a.some();
		System.out.println("Extending with "+ext);
//		sol = sols.branch(2,ext);
		System.out.println(sol.instance());

		solver.free();
	}
	
	@Test
	public void testRegularIteration() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		String aux = sol.instance().toString();
		
		// held in previous but should still change last
		Formula ext = b.eq(b);
		System.out.println("Extending with "+ext);
//		sol = sols.branch(3,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		assertEquals(aux, sol.instance().toString());
		
		// held in previous but should still change last, but no more with same length
		ext = b.eq(b);
		System.out.println("Extending with "+ext);
//		sol = sols.branch(3,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		assertEquals(aux, sol.instance().toString());

		// held in previous but should still change last, but no more with same length
		ext = b.eq(b);
		System.out.println("Extending with "+ext);
//		sol = sols.branch(3,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		assertEquals(aux, sol.instance().toString());

		// held in previous but should still change last, but no more with same length
		ext = b.eq(b);
		System.out.println("Extending with "+ext);
//		sol = sols.branch(3,ext);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());
		assertEquals(aux, sol.instance().toString());

		solver.free();
	}
	
	@Test
	public void testLonger() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((a.eq(a))).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());
		
		// expand beyond prefix size, unrolls but must still expand
		Formula ext = b.eq(b);
		System.out.println("Extending with "+ext);
//		sol = sols.branch(8,ext);
		System.out.println(sol.instance());
		assertEquals(8, ((TemporalInstance) sol.instance()).prefixLength());
		assertEquals(((TemporalInstance) sol.instance()).state(2).toString(), ((TemporalInstance) sol.instance()).state(3).toString());
		assertEquals(((TemporalInstance) sol.instance()).state(2).toString(), ((TemporalInstance) sol.instance()).state(5).toString());
		assertEquals(((TemporalInstance) sol.instance()).state(2).toString(), ((TemporalInstance) sol.instance()).state(7).toString());

		sol = sols.branch(4,Collections.singletonMap(b, bs),true);
		System.out.println(sol.instance());
		assertEquals(8, ((TemporalInstance) sol.instance()).prefixLength());

		solver.free();
	}
	
	@Test
	public void testExploreState() {
		int n = 2;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");
		
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		TupleSet bs = f.range(f.tuple("B0"), f.tuple("B"+(n-2)));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((a.eq(a))).always().and(b.some().after()).and(b.no().always().eventually());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(SATFactory.MiniSat);
		PardinusSolver solver = new PardinusSolver(opt);
		
		
		Explorer<Solution> sols = (Explorer<Solution>) solver.solveAll(formula, bounds);
		Solution sol = sols.next();
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());
		
		// expand beyond prefix size, unrolls but must still expand
		sol = sols.branch(3, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(3, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(3, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(3, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(5, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(3, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(4, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertFalse(sol.sat());

		sol = sols.branch(1, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(2, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		sol = sols.branch(0, new HashSet<Relation>(),true);
		System.out.println(sol.instance());
		assertEquals(3, ((TemporalInstance) sol.instance()).prefixLength());

		solver.free();
	}
}