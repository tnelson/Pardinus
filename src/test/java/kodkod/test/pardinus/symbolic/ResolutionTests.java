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
package kodkod.test.pardinus.symbolic;

import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.engine.config.SLF4JReporter;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
public class ResolutionTests {

	Relation r,s,t,u;
	Relation a,b,c,d;
	Universe uni;
	TupleSet as, bs, sa, sb;
	
	@Before 
	public void setup() {
		r = Relation.binary("r");
		s = VarRelation.binary("s");
		t = Relation.nary("t", 3);
		u = VarRelation.nary("u", 3);
		
		a = Relation.unary("a");
		b = VarRelation.unary("b");
		c = Relation.unary("c");
		d = VarRelation.unary("d");
		
		int n = 3;
		Object[] atoms = new Object[n*2];
		for (int i = 0; i < n; i ++)
			atoms[i] = "A"+i;
		for (int i = 0; i < n; i ++)
			atoms[n+i] = "B"+i;
		
		uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		as = f.range(f.tuple("A0"), f.tuple("A"+(n-1)));
		bs = f.range(f.tuple("B0"), f.tuple("B"+(n-1)));
		sa = f.setOf("A0");
		sb = f.setOf("B0");
	}
	
	@Test
	public void test1() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		bnds.bound(a, as);
		bnds.bound(b, Expression.NONE, a);
		bnds.bound(c, b.union(bnds.reify(sa)), b);
		bnds.bound(d, c);
		
		bnds.bound(r, a.product(a), a.product(a));
		bnds.bound(s, a.product(Expression.NONE), a.product(bnds.reify(bs)));
		bnds.bound(t, bnds.reify(sa).product(bnds.reify(sa)).product(bnds.reify(sa)), a.product(b).product(c));
		bnds.bound(u, r.product(bnds.reify(sa)), r.product(b));
		
		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		orcl.bound(a, as);
		orcl.bound(b, as);
		orcl.bound(c, sa, as);
		orcl.bound(d, as);
		orcl.bound(r, as.product(as));
		orcl.bound(s, as.product(bs));
		orcl.bound(t, sa.product(sa).product(sa), as.product(as).product(as));
		orcl.bound(u, as.product(as).product(as));

		assertTrue(compare(bnds,orcl));
	}
	
	@Test
	public void test2() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		bnds.bound(a, as);
		bnds.bound(b, a.union(bnds.reify(sb)));
		bnds.bound(c, bs, bs);
		bnds.bound(d, c.union(b));
		
		bnds.bound(r, (c.product(c)).union(a.product(a)), (c.product(bnds.reify(bs))).union(a.product(a)));
		bnds.bound(s, sb.product(sa), bs.product(as));
		bnds.bound(t, s.product(bnds.reify(bs)), s.product(bnds.reify(bs)));
		
		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		orcl.bound(a, as);
		TupleSet x = as.clone();
		x.addAll(sb);
		orcl.bound(b, x);
		orcl.bound(c, bs, bs);
		x.addAll(bs);
		orcl.bound(d, x);
		x = (as.product(as)).clone();
		x.addAll(bs.product(bs));
		orcl.bound(r, bs.product(bs), x);
		orcl.bound(s, sb.product(sa), bs.product(as));
		orcl.bound(t, sb.product(sa).product(bs), bs.product(as).product(bs));

		assertTrue(compare(bnds,orcl));
	}
	
	// known bug in "difference" expressions
	@Test
	public void test3() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		bnds.bound(a, as);
		bnds.bound(b, as);
		bnds.bound(c, a.difference(b));
		
		Formula f = bnds.resolve(new SLF4JReporter());
		
		PardinusBounds orcl = new PardinusBounds(uni);
		orcl.bound(a, as);
		orcl.bound(b, as);
		orcl.bound(c, as);

		assertTrue(compare(bnds,orcl));
	}
	
	@Test(expected = IllegalArgumentException.class)
	public void test4() {
		PardinusBounds bnds = new PardinusBounds(uni);
		
		bnds.bound(a, as, as);
		bnds.bound(b, bs, bs);
		bnds.bound(c, a, b);
		
		Formula f = bnds.resolve(new SLF4JReporter());

	}
	
	private boolean compare(Bounds b1, Bounds b2) {
		for (Relation r : b1.relations()) {
			if (b1.lowerBound(r).size() != b2.lowerBound(r).size()) return false;
			if (b1.upperBound(r).size() != b2.upperBound(r).size()) return false;
		}
		return true;
	}

}
