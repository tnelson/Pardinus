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

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.DecomposedKodkodSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.BoundedExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.SymmetryP.VariantFormulas;
import kodkod.examples.pardinus.decomp.SymmetryP;
import kodkod.examples.pardinus.decomp.SymmetryP.VariantBounds;
import kodkod.instance.Bounds;
import kodkod.instance.DecompBounds;
import kodkod.util.ints.IntSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * Tests whether the symmetries are being correctly calculated for decomposed
 * problems. Also tests whether every solution is being enumerated.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
@RunWith(Parameterized.class)
public class SymmetryTests {
	DecomposedKodkodSolver dsolver;
	BoundedExtendedOptions opt, opt2;
	Set<IntSet> last;

	@Before
	public void method() throws InterruptedException {

		opt = new BoundedExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.Glucose);
		opt.setDecomposedMode(DMode.HYBRID);
		opt.setThreads(4);
		opt2 = new BoundedExtendedOptions(opt);
		opt2.setRunTarget(false);
		Reporter rep = new Reporter() {
			@Override
			public void translatingToCNF(BooleanFormula circuit) {
			}

			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				System.out.println("to bool: " + formula.toString() + ", "
						+ bounds);
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
			}

			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				last = new HashSet<IntSet>(parts);
				System.out.println("symmetry: " + parts.toString());
			}

			@Override
			public void solvingConfig(Solution solution) {
				System.out.println(solution.outcome()+": "
						+ solution.instance().relationTuples().toString());
			}

			@Override
			public void configOutcome(Solution solution) {
				System.out.println("dproblem: "+solution.outcome());
			}
			
			@Override
			public void amalgOutcome(Solution solution) {
				System.out.println("amalg: "+solution.outcome());
			}
		};
		opt2.setReporter(rep);

		opt.setConfigOptions(opt2);
		opt.setReporter(rep);
		dsolver = new DecomposedKodkodSolver(opt);
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
//				{ VariantBounds.V1, VariantFormulas.V1 },
//				{ VariantBounds.V2, VariantFormulas.V1 },
//				{ VariantBounds.V3, VariantFormulas.V1 },
//				{ VariantBounds.V4, VariantFormulas.V1 },
//				{ VariantBounds.V5, VariantFormulas.V1 },
//				{ VariantBounds.V6, VariantFormulas.V1 },
				{ VariantBounds.V1, VariantFormulas.V2 },
//				{ VariantBounds.V2, VariantFormulas.V2 },
//				{ VariantBounds.V3, VariantFormulas.V2 },
//				{ VariantBounds.V4, VariantFormulas.V2 },
//				{ VariantBounds.V5, VariantFormulas.V2 },
//				{ VariantBounds.V6, VariantFormulas.V2 },
//				{ VariantBounds.V1, VariantFormulas.V3 },
//				{ VariantBounds.V2, VariantFormulas.V3 },
//				{ VariantBounds.V3, VariantFormulas.V3 },
//				{ VariantBounds.V4, VariantFormulas.V3 },
//				{ VariantBounds.V5, VariantFormulas.V3 },
//				{ VariantBounds.V6, VariantFormulas.V3 },
//				{ VariantBounds.V1, VariantFormulas.V4 },
//				{ VariantBounds.V2, VariantFormulas.V4 },
//				{ VariantBounds.V3, VariantFormulas.V4 },
//				{ VariantBounds.V4, VariantFormulas.V4 },
//				{ VariantBounds.V5, VariantFormulas.V4 },
//				{ VariantBounds.V6, VariantFormulas.V4 },
				};
		return Arrays.asList(data);
	}

	@Test
	public void test() {
		int n = 2;

		String[] args = new String[] { n + "", v1.name(), v2.name() };
		DModel model = new SymmetryP(args);

		opt.setBitwidth(model.getBitwidth());
		opt2.setBitwidth(model.getBitwidth());

		final DecompBounds bounds = new DecompBounds(model.bounds1(),
				model.bounds2());
		final Formula formula = model.partition1().and(model.partition2());
		Iterator<Solution> solution ;
		
		System.out.println("----- Solving decomposed -----");
		solution = dsolver.solveAll(formula, bounds);
		int decomp_counter = 0;

		while (solution.hasNext()) {
			Solution sol = solution.next();
			decomp_counter++;
			System.out.print(sol.outcome().toString()+" " + decomp_counter + ": ");
			if (sol.sat())
				System.out.println(sol.instance().relationTuples());
			else
				System.out.println();

		}
		Set<IntSet> decomp_syms = last;

		
		System.out.println("----- Solving in batch -----");
		Solver solver = new Solver(dsolver.options());
		solution = solver.solveAll(formula, bounds.amalgamated());
		int batch_counter = 0;
		while (solution.hasNext()) {
			Solution sol = solution.next();
			batch_counter++;
			System.out.print(sol.outcome().toString()+" " + batch_counter + ": ");
			if (sol.sat())
				System.out.println(sol.instance().relationTuples());
			else
				System.out.println();
		}
		Set<IntSet> batch_syms = last;

		Assert.assertEquals(batch_syms, decomp_syms);
		Assert.assertEquals(batch_counter, decomp_counter);

	}

}
