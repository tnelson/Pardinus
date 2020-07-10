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
package kodkod.test.pardinus;

import static org.junit.Assert.assertEquals;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.config.ConsoleReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import org.junit.Test;
import org.slf4j.LoggerFactory;

/**
 * Tests the reification of states and paths into formulas, needed for default
 * iteration.
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 *
 */
public class ReificationTests {

	/* Static reification. */
	@Test
	public void testStaticReif() {
		TemporalPardinusSolver.SomeDisjPattern = false;
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");

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
		Formula formula = a.some().and(b.some());

		ExtendedOptions opt = new ExtendedOptions();

		opt.setRunTemporal(false);
		opt.setRunDecomposed(false);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A2]], b=[[B2]]}

		assertEquals("((a = $$A2$$) and (b = $$B2$$))", inst.formulate(bounds.clone(), x, formula).toString());

		formula = formula.and(inst.formulate(bounds, x, formula).not());

		solution = solver.solveAll(formula, bounds);

		inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B1], [B2]], $$A2$$=[[A2]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = ($$B1$$ + $$B2$$)))",
				inst.formulate(bounds.clone(), x, formula).toString());

		formula = formula.and(inst.formulate(bounds, x, formula).not());

		solution = solver.solveAll(formula.and(inst.formulate(bounds, x, formula).not()), bounds);

		inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B2]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B1$$=[[B1]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$B0$$=[[B0]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = $$B2$$))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal reification, not all relations relevant, loop not first. */
	@Test
	public void testTmpReif() {
		TemporalPardinusSolver.SomeDisjPattern = false;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always();

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LAST
//		relations: {a=[], b=[]}

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and next((a = none))) and always((((a = (($$A0$$ + $$A1$$) + $$A2$$)) implies next(next((a = (($$A0$$ + $$A1$$) + $$A2$$))))) and ((a = none) implies next(next((a = none)))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LAST
//		relations: {a=[[A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and next(((a = none) and next((a = $$A2$$))))) and always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) implies next(next(next((a = (($$A0$$ + $$A1$$) + $$A2$$)))))) and ((a = none) implies next(next(next((a = none)))))) and ((a = $$A2$$) implies next(next(next((a = $$A2$$))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal reification. */
	@Test
	public void testTmp2Reif() {
		TemporalPardinusSolver.SomeDisjPattern = false;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]]}

		assertEquals(
				"((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and next(always(((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))) and next(next(always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal segment reification. */
	@Test
	public void testTmpSegmentReif() {
		TemporalPardinusSolver.SomeDisjPattern = false;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]]}

		assertEquals("true", inst.formulate(bounds.clone(), x, formula, -1, -1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and next(always(((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and next(next(always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		solver.free();

	}

	/* Temporal segment reification with static configs. */
	@Test
	public void testTmpConfigSegmentReif() {
		int n = 2;
		TemporalPardinusSolver.SomeDisjPattern = false;

		Relation a = Relation.unary("a");
		Relation b = Relation.binary_variable("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)))
				.product(f.range(f.tuple("B0"), f.tuple("B" + (n - 1))));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((b.eq(b.prime()).not())).always().and(a.no());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0], [A1, B1]]}
//		* state 1 LAST
//		relations: {a=[], b=[]}

		assertEquals("(a = none)", inst.formulate(bounds.clone(), x, formula, -1, -1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))) and always((((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) implies next(next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$)))))) and ((b = (none -> none)) implies next(next((b = (none -> none))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"((a = none) and ((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next((b = (none -> none)))", inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0], [A1, B1]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}
//		* state 1
//		relations: {a=[], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}
//		* state 2 LAST
//		relations: {a=[], b=[[A1, B0], [A1, B1]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next(((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))))) and always(((((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) implies next(next(next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))) and ((b = (none -> none)) implies next(next(next((b = (none -> none))))))) and ((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) implies next(next(next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"((a = none) and ((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next((b = (none -> none)))", inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next(((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		solver.free();

	}

	/* Static reification. */
	@Test
	public void testStaticSome() {
		TemporalPardinusSolver.SomeDisjPattern = true;
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");

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
		Formula formula = a.some().and(b.some());

		ExtendedOptions opt = new ExtendedOptions();

		opt.setRunTemporal(false);
		opt.setRunDecomposed(false);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A2]], b=[[B2]]}

		assertEquals("((a = $$A2$$) and (b = $$B2$$))", inst.formulate(bounds.clone(), x, formula).toString());

		formula = formula.and(inst.formulate(bounds, x, formula).not());

		solution = solver.solveAll(formula, bounds);

		inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B1], [B2]], $$A2$$=[[A2]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = ($$B1$$ + $$B2$$)))",
				inst.formulate(bounds.clone(), x, formula).toString());

		formula = formula.and(inst.formulate(bounds, x, formula).not());

		solution = solver.solveAll(formula.and(inst.formulate(bounds, x, formula).not()), bounds);

		inst = solution.next().instance();

		opt.reporter().debug(inst.toString());
//		opt.reporter().debug(inst.formulate(bounds,x,formula));
//		opt.reporter().debug(x);

//		relations: {a=[[A1], [A2]], b=[[B2]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B1$$=[[B1]], $$B2$$=[[B2]], $$A0$$=[[A0]], $$B0$$=[[B0]]}

		assertEquals("((a = ($$A1$$ + $$A2$$)) and (b = $$B2$$))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal reification, not all relations relevant, loop not first. */
	@Test
	public void testTmpSome() {
		TemporalPardinusSolver.SomeDisjPattern = true;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always();

		ExtendedOptions opt = new ExtendedOptions();

		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(false);
		opt.setRunDecomposed(false);
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = none) and next((a = ((A0 + A1) + A2)))) and always((((a = none) implies next(next((a = none)))) and ((a = ((A0 + A1) + A2)) implies next(next((a = ((A0 + A1) + A2))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[[A2]], b=[]}
//		* state 1 LAST
//		relations: {a=[[A0], [A1]], b=[]}
		
		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and (((a = A2) and next((a = (A0 + A1)))) and always((((a = A2) implies next(next((a = A2)))) and ((a = (A0 + A1)) implies next(next((a = (A0 + A1))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal reification. */
	@Test
	public void testTmp2Some() {
		TemporalPardinusSolver.SomeDisjPattern = true;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "nuXmv"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		Instance inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]]}

		assertEquals(
				"(some [A1: one univ, B2: one univ, A2: one univ, B0: one univ, A0: one univ, B1: one univ] | (((((((A1 + B2) + A2) + B0) + A0) + B1) = univ) and ((((a = none) and (b = none)) and next((((a = (A1 + A2)) and (b = B2)) and next(((a = none) and (b = B2)))))) and next(always(((((a = (A1 + A2)) and (b = B2)) implies next(next(((a = (A1 + A2)) and (b = B2))))) and (((a = none) and (b = B2)) implies next(next(((a = none) and (b = B2)))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		inst = solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))) and next(next(always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula).toString());

		solver.free();

	}

	/* Temporal segment reification. */
	@Test
	public void testTmpSegmentSome() {
		TemporalPardinusSolver.SomeDisjPattern = true;
		int n = 3;

		Relation a = Relation.unary_variable("a");
		Relation b = Relation.unary_variable("b");

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
		Formula formula = ((a.eq(a.prime()).not())).always().and(b.no().and(b.some().always().after()));

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[]}
//		* state 1 LOOP
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]]}
//		* state 2 LAST
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]]}

		assertEquals("true", inst.formulate(bounds.clone(), x, formula, -1, -1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and next(always(((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0
//		relations: {a=[[A0], [A1], [A2]], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 1
//		relations: {a=[[A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 2 LOOP
//		relations: {a=[[A0], [A1], [A2]], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}
//		* state 3 LAST
//		relations: {a=[], b=[[B0], [B1], [B2]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$A2$$=[[A2]], $$B0$$=[[B0]], $$B1$$=[[B1]], $$B2$$=[[B2]]}

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))) and next(next(always(((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))) and (((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) implies next(next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = none)) and next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$)))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next(((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))",
				inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next((((a = ($$A1$$ + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next((((a = (($$A0$$ + $$A1$$) + $$A2$$)) and (b = (($$B0$$ + $$B1$$) + $$B2$$))) and next(((a = none) and (b = (($$B0$$ + $$B1$$) + $$B2$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		solver.free();

	}

	/* Temporal segment reification with static configs. */
	@Test
	public void testTmpConfigSegmentSome() {
		int n = 2;
		TemporalPardinusSolver.SomeDisjPattern = true;

		Relation a = Relation.unary("a");
		Relation b = Relation.binary_variable("b");

		Object[] atoms = new Object[n * 2];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;
		for (int i = 0; i < n; i++)
			atoms[n + i] = "B" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));
		TupleSet bs = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)))
				.product(f.range(f.tuple("B0"), f.tuple("B" + (n - 1))));

		PardinusBounds bounds = new PardinusBounds(uni);
		bounds.bound(a, as);
		bounds.bound(b, bs);
		Formula formula = ((b.eq(b.prime()).not())).always().and(a.no());

		ExtendedOptions opt = new ExtendedOptions();

//		opt.setReporter(new ConsoleReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t", "NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);

		Iterator<Solution> solution = solver.solveAll(formula, bounds);

		Map<Object, Expression> x = new HashMap<Object, Expression>();

		TemporalInstance inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0], [A1, B1]]}
//		* state 1 LAST
//		relations: {a=[], b=[]}

		assertEquals("(a = none)", inst.formulate(bounds.clone(), x, formula, -1, -1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))) and always((((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) implies next(next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$)))))) and ((b = (none -> none)) implies next(next((b = (none -> none))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"((a = none) and ((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next((b = (none -> none)))", inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		inst = (TemporalInstance) solution.next().instance();
		opt.reporter().debug(inst.toString());

//		* state 0 LOOP
//		relations: {a=[], b=[[A0, B0], [A0, B1], [A1, B0], [A1, B1]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}
//		* state 1
//		relations: {a=[], b=[], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}
//		* state 2 LAST
//		relations: {a=[], b=[[A1, B0], [A1, B1]], $$A0$$=[[A0]], $$A1$$=[[A1]], $$B0$$=[[B0]], $$B1$$=[[B1]]}

		assertEquals("next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 2).toString());

		assertEquals(
				"(next(next(((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next((b = (none -> none)))))))) and always(((((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) implies next(next(next((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))))))) and ((b = (none -> none)) implies next(next(next((b = (none -> none))))))) and ((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) implies next(next(next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))))",
				inst.formulate(bounds.clone(), x, formula, 2, null).toString());

		assertEquals(
				"((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$)))))))",
				inst.formulate(bounds.clone(), x, formula, 0, 2).toString());

		assertEquals(
				"((a = none) and ((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))",
				inst.formulate(bounds.clone(), x, formula, -1, 2).toString());

		assertEquals("next((b = (none -> none)))", inst.formulate(bounds.clone(), x, formula, 1, 1).toString());

		assertEquals(
				"next(((b = (none -> none)) and next(((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))) and next(((b = (((($$A0$$ -> $$B0$$) + ($$A0$$ -> $$B1$$)) + ($$A1$$ -> $$B0$$)) + ($$A1$$ -> $$B1$$))) and next(((b = (none -> none)) and next((b = (($$A1$$ -> $$B0$$) + ($$A1$$ -> $$B1$$))))))))))))",
				inst.formulate(bounds.clone(), x, formula, 1, 5).toString());

		solver.free();

	}
}
