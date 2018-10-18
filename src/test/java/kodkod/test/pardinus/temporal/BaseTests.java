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
import kodkod.ast.VarRelation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.config.Reporter;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
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
		opt.setSolver(SATFactory.DefaultSAT4J);
		opt.setRunDecomposed(false);
		opt.setRunUnbounded(false);
		opt.setRunTemporal(true);
		Reporter rep = new SLF4JReporter();
		opt.setReporter(rep);
		
		dsolver = new PardinusSolver(opt);
	}

	@Test
	public void testSAT() {
		int n = 2;

		Relation a = VarRelation.unary("a");
		Relation b = Relation.unary("b");
		VarRelation r = VarRelation.binary("r");

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
		
		assert(sol.sat());

	}
	
	@Test
	public void testUNSAT() {
		int n = 2;

		Relation a = VarRelation.unary("a");
		Relation b = Relation.unary("b");
		VarRelation r = VarRelation.binary("r");

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
		
		assert(!sol.sat());

	}

}
