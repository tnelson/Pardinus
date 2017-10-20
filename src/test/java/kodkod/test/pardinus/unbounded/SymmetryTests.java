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
package kodkod.test.pardinus.unbounded;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.temporal.SymmetryT;
import kodkod.examples.pardinus.temporal.SymmetryT.VariantBounds;
import kodkod.examples.pardinus.temporal.SymmetryT.VariantFormulas;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.Tuple;
import kodkod.util.ints.IntSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Tests whether the symmetries are being correctly calculated for decomposed
 * problems by comparing with the amalgamated problem, as well as whether every
 * solution is being enumerated. Also tests problems where either the partial or
 * integrated problem become trivial. Uses the models from {@link SymmetryP}.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
@RunWith(Parameterized.class)
public class SymmetryTests {
	private PardinusSolver dsolver;
	private ExtendedOptions opt;
	private Set<IntSet> last;

	@Before
	public void method() throws InterruptedException {

		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.HYBRID);
		opt.setThreads(4);
		Reporter rep = new Reporter() {
		    private Logger LOGGER = LoggerFactory.getLogger(Reporter.class);

			private Bounds bounds;

			@Override
			public void translatingToCNF(BooleanFormula circuit) {
			}

			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				LOGGER.debug("to bool: " + formula.toString() + ", "
						+ bounds.toString().replaceAll("[\r\n]+", " "));
			}

			@Override
			public void solvingCNF(int primaryVars, int vars, int clauses) {
			}

			@Override
			public void skolemizing(Decl decl, Relation skolem,
					List<Decl> context) {
			}

			@Override
			public void optimizingBoundsAndFormula() {
			}

			@Override
			public void generatingSBP() {
			}

			@Override
			public void detectingSymmetries(Bounds bounds) {
				this.bounds = bounds;
			}

			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				last = new HashSet<IntSet>(parts);
				Set<Set<Object>> x = new HashSet<Set<Object>>();
				for (IntSet y : parts) {
					Set<Object> z = new HashSet<Object>();
					for (int w : y.toArray())
						z.add(bounds.universe().atom(w));
					x.add(z);
				}
				LOGGER.debug("symmetry: " + x.toString());
			}

			@Override
			public void reportLex(List<Entry<Relation, Tuple>> _original,
					List<Entry<Relation, Tuple>> _permuted) {
				LOGGER.debug("lex: "+_original.toString() + " < " + _permuted.toString());
				
			}
			
			@Override
			public void debug(String debug) {
				LOGGER.debug(debug);
			}

		};

		opt.setReporter(rep);
	}

	private VariantBounds v1;
	private VariantFormulas v2;

	public SymmetryTests(VariantBounds v1, VariantFormulas v2) {
		this.v1 = v1;
		this.v2 = v2;
	}

	@Parameters(name = "{0} {1}")
	public static Collection<Object[]> data() {
		Object[][] data = new Object[][] {
				{ VariantBounds.V1, VariantFormulas.V1 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V1 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V1 }, // unsat, p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V2 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V2 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V2 }, // unsat, p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
				};
		return Arrays.asList(data);
	}

	@Test
	public void test() {
		int n = 3;

		String[] args = new String[] { n + "", v1.name(), v2.name() };
		DModel model = new SymmetryT(args);

		opt.setBitwidth(model.getBitwidth());
		opt.setRunUnbounded(true);
		opt.setRunTemporal(true);
		opt.setRunDecomposed(true);
		opt.setDecomposedMode(DMode.PARALLEL);
		dsolver = new PardinusSolver(opt);
		final PardinusBounds bounds = model.bounds1();
		bounds.merge(model.bounds2());
		final Formula formula = model.partition1().and(model.partition2());
		Solution sol;
		
		System.out.println("----- Solving decomposed -----");
		sol = dsolver.solve(formula, bounds);
		int decomp_counter = 0;

		decomp_counter++;
		System.out.print(sol.outcome().toString()+" " + decomp_counter + ": ");
		if (sol.sat())
			System.out.println(sol.instance().relationTuples());
		else
			System.out.println();

		Set<IntSet> decomp_syms = last;

		System.out.println("----- Solving in batch -----");

		opt.setRunDecomposed(false);
		PardinusSolver solver = new PardinusSolver(opt);
		sol = solver.solve(formula, bounds);
		int batch_counter = 0;
		batch_counter++;
		System.out.print(sol.outcome().toString()+" " + batch_counter + ": ");
		if (sol.sat())
			System.out.println(sol.instance().relationTuples());
		else
			System.out.println();
		Set<IntSet> batch_syms = last;

		// if config is trivially unsat, then time symmetries are not found on partial problem
		Assert.assertTrue(batch_syms.equals(decomp_syms) || (decomp_counter == 1 && batch_syms.size() == decomp_syms.size()+1));
		Assert.assertEquals(batch_counter, decomp_counter);

	}

}
