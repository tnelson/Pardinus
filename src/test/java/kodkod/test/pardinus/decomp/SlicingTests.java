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

import java.util.Map.Entry;

import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Relation;
import kodkod.engine.decomp.DecompFormulaSlicer;
import kodkod.examples.pardinus.decomp.SymmetryP;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Universe;

import org.junit.Assert;
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
public class SlicingTests {

	Relation r = Relation.unary("r");
	Relation s = Relation.unary("s");
	Relation t = Relation.unary("t");
	
	@Test
	public void test1() {
		Formula f1 = r.one();
		Formula f2 = s.one();
		Formula f3 = t.one();

		Formula f4 = f2.or(f3);
		Formula f = f1.and(f4);
		
		Universe universe = new Universe("A");
		PardinusBounds b1 = new PardinusBounds(universe);
		PardinusBounds b2 = new PardinusBounds(universe);
		b1.bound(r, universe.factory().allOf(1));
		b1.bound(s, universe.factory().allOf(1));
		b2.bound(t, universe.factory().allOf(1));

		PardinusBounds b = new PardinusBounds(b1,b2);
		
		Entry<Formula, Formula> fs = DecompFormulaSlicer.slice(f, b);
		
		Assert.assertEquals(f1, fs.getKey());
		Assert.assertEquals(f4, fs.getValue());
	}

	@Test
	public void test2() {
		Formula f1 = r.one();
		Formula f2 = s.one();
		Formula f3 = t.one();

		Formula f4 = f2.or(f3);
		Formula f = NaryFormula.and(f1,f4);
		
		Universe universe = new Universe("A");
		PardinusBounds b1 = new PardinusBounds(universe);
		PardinusBounds b2 = new PardinusBounds(universe);
		b1.bound(r, universe.factory().allOf(1));
		b1.bound(s, universe.factory().allOf(1));
		b2.bound(t, universe.factory().allOf(1));

		PardinusBounds b = new PardinusBounds(b1,b2);
		
		Entry<Formula, Formula> fs = DecompFormulaSlicer.slice(f, b);
		
		Assert.assertEquals(f1, fs.getKey());
		Assert.assertEquals(f4, fs.getValue());
	}

	@Test
	public void test3() {
		Formula f1 = r.one();
		Formula f2 = s.one();
		Formula f3 = t.one();

		Formula f4 = (f2.or(f3)).not();
		Formula f = NaryFormula.and(f1,f4);
		
		Universe universe = new Universe("A");
		PardinusBounds b1 = new PardinusBounds(universe);
		PardinusBounds b2 = new PardinusBounds(universe);
		b1.bound(r, universe.factory().allOf(1));
		b1.bound(s, universe.factory().allOf(1));
		b2.bound(t, universe.factory().allOf(1));

		PardinusBounds b = new PardinusBounds(b1,b2);
		
		Entry<Formula, Formula> fs = DecompFormulaSlicer.slice(f, b);
		
		Assert.assertEquals(f1.and(f2.not()), fs.getKey());
		Assert.assertEquals(f3, fs.getValue());
	}
}
