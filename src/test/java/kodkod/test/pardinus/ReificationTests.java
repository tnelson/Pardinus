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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.SymmetryP;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
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
public class ReificationTests {

	@Test
	public void test() {
		int n = 3;

		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		
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
		Formula formula = a.some().and(b.some());

		ExtendedOptions opt = new ExtendedOptions();

		opt.setRunTemporal(false);
		opt.setRunDecomposed(false);
		PardinusSolver solver = new PardinusSolver(opt);
		
		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		
		Map<Object, Expression> x = new HashMap<Object,Expression>();
		
		Instance inst = solution.next().instance();

		System.out.println(inst.toString());
		System.out.println(inst.formulate(x));
		System.out.println(x);
		
		formula = formula.and(inst.formulate(x).not());

		solution = solver.solveAll(formula, bounds);
		
		inst = solution.next().instance();
		
		System.out.println(inst.toString());
		System.out.println(inst.formulate(x));
		System.out.println(x);
	
		formula = formula.and(inst.formulate(x).not());

		solution = solver.solveAll(formula.and(inst.formulate(x).not()), bounds);

		inst = solution.next().instance();

		System.out.println(inst.toString());
		System.out.println(inst.formulate(x));
		System.out.println(x);

		solver.free();

	}
	
	@Test
	public void testTmp() {
		int n = 3;

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
		Formula formula = ((a.eq(a.prime()).not())).always();

		ExtendedOptions opt = new ExtendedOptions();

		opt.setReporter(new SLF4JReporter());
		opt.setRunTemporal(true);
		opt.setRunUnbounded(true);
		opt.setRunDecomposed(false);
		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
		PardinusSolver solver = new PardinusSolver(opt);
		
		Iterator<Solution> solution = solver.solveAll(formula, bounds);
		
		System.out.println(solution.next().instance());
		System.out.println(solution.next().instance());
		System.out.println(solution.next().instance());
		System.out.println(solution.next().instance());
		
		solver.free();

	}

}
