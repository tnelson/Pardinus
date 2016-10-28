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
package kodkod.examples.pardinus.decomp;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.decomp.DModel;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/**
 * Examples for testing whether the symmetries are being correctly calculated for decomposed
 * problems. 
 * 
 * @see kodkod.test.pardinus.decomp.SymmetryTests
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */public final class SymmetryP implements DModel {

	final private int n,m;

//	private final Relation a, b; //
	private final Relation r, s;
	private final Universe u;
	
	public enum VariantBounds {
		V1, V2, V3, V4, V5, V6;
	}
	
	public enum VariantFormulas {
		V1, V2, V3, V4;
	}

	VariantBounds v1;
	VariantFormulas v2;
	
	public SymmetryP(String[] args) {
		this.n = Integer.valueOf(args[0]);
		this.m = n;
		this.v1 = VariantBounds.valueOf(args[1]);
		this.v2 = VariantFormulas.valueOf(args[2]);
		
//		a = Relation.unary("a"); //
//		b = Relation.unary("b"); //

		r = Relation.unary("r");
		s = Relation.unary("s");

		final List<String> atoms = new ArrayList<String>(2*n);
		for(int i = 0; i < m; i++)
			atoms.add("A"+i);
//		for(int i = 0; i < n-1; i++)
//			atoms.add("B"+i);
//		
		u = new Universe(atoms);
	}

	@Override
	public Bounds bounds1() {
		final TupleFactory f = u.factory();
		final Bounds bnd = new Bounds(u);
		
		final TupleSet upper_a = f.range(f.tuple("A0"), f.tuple("A"+ (m-1)));
//		final TupleSet upper_b = f.range(f.tuple("B0"), f.tuple("B"+ (m-2)));
		final TupleSet lower_a = f.noneOf(1);
//
//		if (v1 == VariantBounds.V3 || v1 == VariantBounds.V4 || v1 == VariantBounds.V5)
//			lower_a.add(f.tuple("A0"));
//
//		if (v1 == VariantBounds.V5 || v1 == VariantBounds.V6)
//			lower_a.add(f.tuple("A"+(m-1)));
//
//		final TupleSet upper_r = upper_a.product(upper_b);
//		final TupleSet lower_r = f.noneOf(2);
//
//		if (v1 == VariantBounds.V2)
//			lower_r.addAll(lower_a.product(lower_a));
//
//		if (v1 == VariantBounds.V4)
//			lower_r.addAll(upper_a.product(upper_a));

//		bnd.bound(a, lower_a, upper_a); //
		bnd.bound(r, upper_a);
		
		return bnd;	
	}

	@Override
	public Bounds bounds2() {
		final TupleFactory f = u.factory();
		final Bounds bnd = new Bounds(u);
		
		final TupleSet upper_a = f.range(f.tuple("A0"), f.tuple("A"+ (m-1)));
//		final TupleSet upper_b = f.range(f.tuple("B0"), f.tuple("B"+ (n-2)));
		

//		final TupleSet lower_b = f.noneOf(1);
//		final TupleSet upper_s = upper_a.product(upper_b);
		final TupleSet lower_s = f.noneOf(2);
//
//		if (v1 == VariantBounds.V2 || v1 == VariantBounds.V5)
//			lower_s.addAll(f.setOf(f.tuple("A0")).product(upper_b));
//
//		if (v1 == VariantBounds.V6)
//			lower_s.addAll(f.range(f.tuple("A1"), f.tuple("A"+ (m-1))).product(upper_b));
//
//		bnd.bound(b, lower_b, upper_b); //
		bnd.bound(s,upper_a);
				
		return bnd;	
	}

	@Override
	public Formula partition1() {
//		Formula x13 = r.in(a.product(a)); //
		Formula x15 = r.one();
		
		Formula x12=x15;
		return (v2==VariantFormulas.V1 || v2==VariantFormulas.V2)?x12:Formula.TRUE;
	}

	@Override
	public Formula partition2() {
//		Formula x13 = s.in(a.product(b)); //
		Formula x14 = s.one(); 

		Formula f2 =x14;
		return (v2==VariantFormulas.V2 || v2==VariantFormulas.V3)?f2:Formula.TRUE;
	}


	@Override
	public int getBitwidth() {
		return 1;
	}

	@Override
	public String shortName() {
		return "Symmetry "+n;
	}






}
