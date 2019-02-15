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
package kodkod.engine;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATProver;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.satlab.WTargetSATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;
import kodkod.util.nodes.PrettyPrinter;

/**
 * A temporal solver relying on Kodkod.
 * 
 * The solver is responsible by iteratively increasing the bounded trace length
 * up to the maximum defined in the options. Adapted from {@link kodkod.engine.Solver}.
 * 
 * @author Nuno Macedo // [HASLab] target-oriented and temporal model finding
 */
public final class TemporalPardinusSolver implements KodkodSolver<PardinusBounds, ExtendedOptions>,
		TemporalSolver<ExtendedOptions> {
	private final ExtendedOptions options;

	/**
	 * Constructs a new Solver with the default options.
	 * 
	 * @ensures this.options' = new Options()
	 */
	public TemporalPardinusSolver() {
		this.options = new ExtendedOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * 
	 * @ensures this.options' = options
	 * @throws NullPointerException
	 *             options = null
	 */
	public TemporalPardinusSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();
		
		assert !options.decomposed();
		
		this.options = options;
	}

	/**
	 * Returns the Options object used by this Solver to guide translation of
	 * formulas from first-order logic to cnf.
	 * 
	 * @return this.options
	 */
	public ExtendedOptions options() {
		return options;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see kodkod.engine.KodkodSolver#free()
	 */
	public void free() {
	}

	// [HASLab]
	public Solution solve(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {
		assert !options.unbounded();
		try {
			long startTransl = System.currentTimeMillis();
			
			// [HASLab] if not decomposed, use the amalgamated if any
			if (!options.decomposed() && bounds.amalgamated!=null)
				bounds = bounds.amalgamated();
			
			// [HASLab] retrieve the additional formula imposed by the symbolic
			// bounds, depending on execution stage
			Formula symbForm = Formula.TRUE;
			// [HASLab] if decomposed mode, the amalgamated bounds are always considered
			if (options.decomposed() && bounds.amalgamated() != null)
				symbForm = bounds.amalgamated().resolve(options.reporter());
			// [HASLab] otherwise use regular bounds
			else
				symbForm = bounds.resolve(options.reporter());

			TemporalTranslator tmptrans = new TemporalTranslator(formula, bounds);
			Formula extformula = tmptrans.translate();
			long endTransl = System.currentTimeMillis();
			long transTime = endTransl - startTransl;
			boolean isSat = false;
			long solveTime = 0;
			Translation.Whole translation = null;
			int traceLength = options.minTraceLength()-1;
			while (!isSat && traceLength <= options.maxTraceLength()) {
				startTransl = System.currentTimeMillis();
				// increase while UNSAT and below max
				do {
					traceLength++;
					Bounds extbounds = tmptrans.expand(traceLength);
					translation = Translator.translate(extformula, extbounds, options);
				} while (translation.trivial() && traceLength <= options.maxTraceLength());

				endTransl = System.currentTimeMillis();
				transTime += endTransl - startTransl;

				if (translation.trivial() && traceLength == options.maxTraceLength())
					return trivial(translation, endTransl - startTransl, tmptrans);
				
				final SATSolver cnf = translation.cnf();

				options.reporter().solvingCNF(translation.numPrimaryVariables(), cnf.numberOfVariables(),
						cnf.numberOfClauses());
				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime += endSolve - startSolve;
				traceLength++;
			}
			final Statistics stats = new Statistics(translation, transTime, solveTime);
			return isSat ? sat(translation, stats, tmptrans) : unsat(translation, stats);
		} catch (SATAbortedException sae) {
			throw new AbortedException(sae);
		}
	}

	public Iterator<Solution> solveAll(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {
		if (Options.isDebug())
			flushFormula(formula, bounds); // [AM]

		// [HASLab] this was commented, why?
		if (!options.solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");

		if (options instanceof ExtendedOptions && options.targetoriented())
			return new TSolutionIterator(formula, bounds, options); // [HASLab]
		else
			return new SolutionIterator(formula, bounds, options);
	}

	// [AM]
	private void flushFormula(Formula formula, Bounds bounds) {
		try {
			File f = new File(System.getProperty("java.io.tmpdir"), "kk.txt");
			OutputStream os = new BufferedOutputStream(new FileOutputStream(f));
			os.write(PrettyPrinter.print(formula, 2).getBytes());
			os.write("\n================\n".getBytes());
			os.write(bounds.toString().getBytes());
			os.flush();
			os.close();
		} catch (Exception e) {
		}
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return options.toString();
	}

	// [HASLab]
	private static Solution sat(Translation.Whole translation, Statistics stats, TemporalTranslator originalBounds) {
		final Solution sol = Solution.satisfiable(stats, new TemporalInstance(translation.interpret(),originalBounds));
		translation.cnf().free();
		return sol;
	}

	// [HASLab]
	private static Solution unsat(Translation.Whole translation, Statistics stats) {
		final SATSolver cnf = translation.cnf();
		final TranslationLog log = translation.log();
		if (cnf instanceof SATProver && log != null) {
			return Solution.unsatisfiable(stats, new ResolutionBasedProof((SATProver) cnf, log));
		} else { // can free memory
			final Solution sol = Solution.unsatisfiable(stats, null);
			cnf.free();
			return sol;
		}
	}

	// [HASLab]
	private static Solution trivial(Translation.Whole translation, long translTime, TemporalTranslator originalBounds) {
		final Statistics stats = new Statistics(0, 0, 0, translTime, 0);
		final Solution sol;
		if (translation.cnf().solve()) {
			sol = Solution.triviallySatisfiable(stats, new TemporalInstance(translation.interpret(),originalBounds));
		} else {
			sol = Solution.triviallyUnsatisfiable(stats, trivialProof(translation.log()));
		}
		translation.cnf().free();
		return sol;
	}

	/**
	 * Returns a proof for the trivially unsatisfiable log.formula, provided
	 * that log is non-null. Otherwise returns null.
	 * 
	 * @requires log != null => log.formula is trivially unsatisfiable
	 * @return a proof for the trivially unsatisfiable log.formula, provided
	 *         that log is non-null. Otherwise returns null.
	 */
	private static Proof trivialProof(TranslationLog log) {
		return log == null ? null : new TrivialProof(log);
	}

	/**
	 * An iterator over all solutions of a model.
	 * 
	 * @author Nuno Macedo // [HASLab] temporal model finding
	 */
	private final static class SolutionIterator implements Iterator<Solution> {
		private Translation.Whole translation;
		private Formula extformula; 
		private int unrolls;
		private long translTime;
		private int trivial;
		private final PardinusBounds tempBounds;
		private final ExtendedOptions opt; // [HASLab] temporal
		private int current_trace;
		private boolean incremented = false;
		private TemporalTranslator tmptrans;
		private Set<TemporalInstance> previous_instances = new HashSet<TemporalInstance>(); // [HASLab]
		
		SolutionIterator(Formula formula, PardinusBounds bounds, ExtendedOptions options) { // [HASLab]
			assert !options.unbounded();
			this.translTime = System.currentTimeMillis();
			current_trace = options.minTraceLength()-1;
			do {
				current_trace++;

				// [HASLab] if not decomposed, use the amalgamated if any
				if (!options.decomposed() && bounds.amalgamated!=null)
					bounds = bounds.amalgamated();

				// [HASLab] retrieve the additional formula imposed by the symbolic
				// bounds, depending on execution stage
				Formula symbForm = Formula.TRUE;
				// [HASLab] if decomposed mode, the amalgamated bounds are always considered
				if (options.decomposed() && bounds.amalgamated() != null)
					symbForm = bounds.amalgamated().resolve(options.reporter());
				// [HASLab] otherwise use regular bounds
				else
					symbForm = bounds.resolve(options.reporter());

				this.tmptrans = new TemporalTranslator(formula.and(symbForm), bounds);
				Bounds extbounds = tmptrans.expand(current_trace);
				this.extformula = tmptrans.translate();
				this.translation = Translator.translate(extformula, extbounds, options);
			} while (this.translation.trivial() && current_trace <= options.maxTraceLength());

			this.translTime = System.currentTimeMillis() - translTime;
			this.trivial = 0;
			this.tempBounds = bounds;
			this.opt = options;
		}

		/**
		 * Returns true if there is another solution.
		 * 
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return translation != null;
		}

		/**
		 * Returns the next solution if any.
		 * 
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			if (!hasNext())
				throw new NoSuchElementException();
			try {
				Solution sol = translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution(); 
				if (sol.sat()) previous_instances.add((TemporalInstance) sol.instance());
				return sol;
			} catch (SATAbortedException sae) {
				translation.cnf().free();
				throw new AbortedException(sae);
			}
		}

		/** @throws UnsupportedOperationException */
		public void remove() {
			throw new UnsupportedOperationException();
		}

		/**
		 * Solves {@code translation.cnf} and adds the negation of the found
		 * model to the set of clauses. The latter has the effect of forcing the
		 * solver to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 * 
		 * @requires this.translation != null
		 * @ensures this.translation.cnf is modified to eliminate the current
		 *          solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextNonTrivialSolution() {
			boolean isSat = false;
			long solveTime = 0;
			Translation.Whole transl = null;
			int primaryVars = -1;
			SATSolver cnf = null;

			boolean mode = false;
			
			while (!isSat && current_trace <= opt.maxTraceLength()) {
				if (incremented) {
					opt.reporter().debug("Trace length incremented to "+current_trace);
					
					if (!mode) {
						for(TemporalInstance inst : previous_instances) {
							Map<Object,Expression> reifs = new HashMap<Object,Expression>();
							Formula aux = inst.formulate(reifs);
							aux = new TemporalTranslator(aux, tmptrans.bounds).translate();
							extformula = extformula.and(aux);
							for (Object o : reifs.keySet()) {
								Expression e = reifs.get(o);
								if (e instanceof Relation)
								tmptrans.bounds.boundExactly((Relation) e,tmptrans.bounds.universe().factory().setOf(o));

							}
						}
					}
					
					long translStart = System.currentTimeMillis();
					translation = Translator.translate(extformula, tmptrans.expand(current_trace), opt);
					long translEnd = System.currentTimeMillis();
					translTime += translEnd - translStart;
					incremented = false;
					if (mode) {
						for(TemporalInstance inst : previous_instances) {
							Set<TemporalInstance> insts = inst.unrollStep(current_trace);
							System.out.println("Expanding and negating previous instance, "+insts.size()+" possible unrolls:\n"+inst);
							TemporalInstance inste = insts.iterator().next();
							List<Integer> notModel = new ArrayList<Integer>();
							int j = 0;
							for (Relation r : translation.bounds().relations()) {
								TupleSet lower = translation.bounds().lowerBound(r);
								IntSet vars = translation.primaryVariables(r);
								if (!vars.isEmpty() && !r.equals(TemporalTranslator.LOOP)&& inste.tuples(r) != null) {
									System.out.print(r+" has vars "+vars+", result is ");
									int lit = vars.min();
									for(IntIterator iter = translation.bounds().upperBound(r).indexView().iterator(); iter.hasNext();) {
										final int index = iter.next();
										if (!lower.indexView().contains(index)) {
											notModel.add(inste.tuples(r).indexView().contains(index)?-lit:lit);
											System.out.print(notModel);
											lit++;
										}
									}
									System.out.println("\n");
								}
							}
							System.out.println("New clause without loops");
							for (int i = 0; i < notModel.size(); i++)
								System.out.print(notModel.get(i)+" ");
							System.out.println("");
							Set<Integer> loops = new HashSet<Integer>();
							IntSet vars = translation.primaryVariables(TemporalTranslator.LOOP);
							for (TemporalInstance i : insts) {
								int lit = vars.min();
								for(IntIterator iter = translation.bounds().upperBound(TemporalTranslator.LOOP).indexView().iterator(); iter.hasNext();) {
									final int index = iter.next();
									if (i.tuples(TemporalTranslator.LOOP).indexView().contains(index)) loops.add(lit);
									lit++;
								}
								System.out.println("");
							}
							System.out.println("Bad loops were "+loops);
							for(IntIterator iter = vars.iterator(); iter.hasNext();) {
								final int lit = iter.next();
								if (!loops.contains(lit)) notModel.add(lit);
							}
							System.out.println("New final clause");
							for (int k = 0; k < notModel.size(); k++)
								System.out.print(notModel.get(k)+" ");
							System.out.println("");
	
							translation.cnf().addClause(notModel.stream().mapToInt(ii->ii).toArray());
						} 
					}
				}
				
				transl = translation;

				cnf = transl.cnf();
				primaryVars = transl.numPrimaryVariables();

				transl.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime += endSolve - startSolve;
				
				if (!isSat) {
					current_trace++;
					incremented = true;
				}
			}

			final Statistics stats = new Statistics(transl, translTime, solveTime);
			final Solution sol;

			if (isSat) {
				// extract the current solution; can't use the sat(..) method
				// because it frees the sat solver
				sol = Solution.satisfiable(stats, new TemporalInstance(transl.interpret(),tmptrans));
				System.out.print("New solution\n"+sol.instance()+ "which negated is ");
				// add the negation of the current model to the solver
				final int[] notModel = new int[primaryVars];
				for (int i = 1; i <= primaryVars; i++) {
					notModel[i - 1] = cnf.valueOf(i) ? -i : i;
					System.out.print(notModel[i - 1]+" ");
				}
				System.out.println("");
				cnf.addClause(notModel);
			} else {
				sol = unsat(transl, stats); // this also frees up solver resources, if any
				translation = null; // unsat, no more solutions
			}
			return sol;
		}

		/**
		 * Returns the trivial solution corresponding to the trivial translation
		 * stored in {@code this.translation}, and if
		 * {@code this.translation.cnf.solve()} is true, sets
		 * {@code this.translation} to a new translation that eliminates the
		 * current trivial solution from the set of possible solutions. The
		 * latter has the effect of forcing either the translator or the solver
		 * to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 * 
		 * @requires this.translation != null
		 * @ensures this.translation is modified to eliminate the current
		 *          trivial solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextTrivialSolution() {
			final Translation.Whole transl = this.translation;

			final Solution sol = trivial(transl, translTime, tmptrans); // this also frees up solver resources, if unsat

			if (sol.instance() == null) {
				translation = null; // unsat, no more solutions
			} else {
				trivial++;

				final Bounds bounds = transl.bounds();
				final Bounds newBounds = bounds.clone();
				final List<Formula> changes = new ArrayList<Formula>();

				for (Relation r : bounds.relations()) {
					final TupleSet lower = bounds.lowerBound(r);

					if (lower != bounds.upperBound(r)) { // r may change
						if (lower.isEmpty()) {
							changes.add(r.some());
						} else {
							final Relation rmodel = Relation.nary(r.name() + "_" + trivial, r.arity());
							newBounds.boundExactly(rmodel, lower);
							changes.add(r.eq(rmodel).not());
						}
					}
				}

				// nothing can change => there can be no more solutions (besides
				// the current trivial one).
				// note that transl.formula simplifies to the constant true with
				// respect to
				// transl.bounds, and that newBounds is a superset of
				// transl.bounds.
				// as a result, finding the next instance, if any, for
				// transl.formula.and(Formula.or(changes))
				// with respect to newBounds is equivalent to finding the next
				// instance of Formula.or(changes) alone.
				final Formula formula = changes.isEmpty() ? Formula.FALSE : Formula.or(changes);

				final long startTransl = System.currentTimeMillis();
				translation = Translator.translate(formula, newBounds, transl.options());
				translTime += System.currentTimeMillis() - startTransl;
			}
			return sol;
		}

	}

	/**
	 * A target-oriented iterator over all solutions of a model, adapted from {@link SolutionIterator}.
	 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented, temporal model finding
	 */
	public static class TSolutionIterator implements Iterator<Solution> {
		private Translation.Whole translation;
		private long translTime;
		private final ExtendedOptions opt; // [HASLab] TO mode
		private Map<String, Integer> weights; // [HASLab] signature weights
		private final PardinusBounds tempBounds;
		private final Formula extformula;
		private TemporalTranslator tmptrans;

		TSolutionIterator(Formula formula, PardinusBounds bounds, ExtendedOptions options) { // [HASLab]
			if (!options.configOptions().solver().maxsat())
				throw new IllegalArgumentException("A max sat solver is required for target-oriented solving.");
			this.translTime = System.currentTimeMillis();
			tmptrans = new TemporalTranslator(formula, bounds);
			Bounds extbounds = tmptrans.expand(1);
			this.extformula = tmptrans.translate();
			this.translation = Translator.translate(extformula, extbounds, options);
			this.translTime = System.currentTimeMillis() - translTime;
			this.opt = options;
			this.tempBounds = bounds;
		}

		/**
		 * Returns true if there is another solution.
		 * 
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return translation != null;
		}

		/**
		 * Returns the next solution if any.
		 * 
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			if (!hasNext())
				throw new NoSuchElementException();
			// TODO [HASLab]: trivial solutions not yet supported in TO
			if (translation.trivial())
				throw new RuntimeException("Trivial problems with targets not yet supported.");
			else
				try {
					return translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution();
				} catch (SATAbortedException sae) {
					translation.cnf().free();
					throw new AbortedException(sae);
				}
		}

		/** @throws UnsupportedOperationException */
		public void remove() {
			throw new UnsupportedOperationException();
		}

		/**
		 * Solves {@code translation.cnf} and adds the negation of the found
		 * model to the set of clauses. The latter has the effect of forcing the
		 * solver to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 * 
		 * @requires this.translation != null
		 * @ensures this.translation.cnf is modified to eliminate the current
		 *          solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextNonTrivialSolution() {
			final TMode mode = opt.targetMode();
			boolean isSat = false;
			int traceLength = opt.minTraceLength();
			long solveTime = 0;
			Translation.Whole transl = null;
			int primaryVars = -1;
			SATSolver cnf = null;
			while (!isSat && traceLength <= opt.maxTraceLength()) {
				if (traceLength > 1) {
					long translStart = System.currentTimeMillis();
					Bounds extbounds = tmptrans.expand(1);
					translation = Translator.translate(extformula, extbounds, opt);
					long translEnd = System.currentTimeMillis();
					translTime += translEnd - translStart;
				}
				transl = translation;

				cnf = transl.cnf();
				primaryVars = transl.numPrimaryVariables();
				// [HASLab] add the targets to generate the following
				// solution due to the architecture of Alloy, targets are added
				// directly
				// to the SAT rather than through the bounds
				try {
					cnf.valueOf(1); // fails if no previous solution
					final int[] notModel = new int[primaryVars];
					if (mode.equals(TMode.CLOSE) || mode.equals(TMode.FAR)) {
						TargetSATSolver tcnf = (TargetSATSolver) cnf;
						tcnf.clearTargets();
						// [HASLab] if there are weights must iterate
						// through the relations to find the literal's owner
						if (weights != null) {
							WTargetSATSolver wcnf = (WTargetSATSolver) cnf;
							for (Relation r : transl.bounds().relations()) {
								Integer w = weights.get(r.name());
								if (r.name().equals("Int/next") || r.name().equals("seq/Int")
										|| r.name().equals("String")) {
								} else {
									if (w == null) {
										w = 1;
									}
									IntIterator is = transl.primaryVariables(r).iterator();
									while (is.hasNext()) {
										int i = is.next();
										// add the negation of the current model
										// to the solver
										notModel[i - 1] = cnf.valueOf(i) ? -i : i;
										// [HASLab] add current model
										// as weighted target
										if (mode == TMode.CLOSE)
											wcnf.addWeight(cnf.valueOf(i) ? i : -i, w);
										if (mode == TMode.FAR)
											wcnf.addWeight(cnf.valueOf(i) ? -i : i, w);
									}
								}
							}
						}
						// [HASLab] if there are no weights may simply
						// iterate literals
						else {
							for (int i = 1; i <= primaryVars; i++) {
								// add the negation of the current model to the
								// solver
								notModel[i - 1] = cnf.valueOf(i) ? -i : i;
								// [HASLab] add current model as target
								if (mode == TMode.CLOSE)
									tcnf.addTarget(cnf.valueOf(i) ? i : -i);
								if (mode == TMode.FAR)
									tcnf.addTarget(cnf.valueOf(i) ? -i : i);
							}
						}

					} else {
						for (int i = 1; i <= primaryVars; i++) {
							// add the negation of the current model to the
							// solver
							notModel[i - 1] = cnf.valueOf(i) ? -i : i;
						}
					}
					cnf.addClause(notModel);
				} catch (IllegalStateException e) {
				} catch (Exception e) {
					throw e;
				}

				opt.reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime += endSolve - startSolve;
			}
			final Statistics stats = new Statistics(transl, translTime, solveTime);
			final Solution sol;

			if (isSat) {
				// extract the current solution; can't use the sat(..) method
				// because it frees the sat solver
				sol = Solution.satisfiable(stats, new TemporalInstance(transl.interpret(),tmptrans));
			} else {
				sol = unsat(transl, stats); // this also frees up solver
											// resources, if any
				translation = null; // unsat, no more solutions
			}
			return sol;
		}

		/**
		 * Returns the trivial solution corresponding to the trivial translation
		 * stored in {@code this.translation}, and if
		 * {@code this.translation.cnf.solve()} is true, sets
		 * {@code this.translation} to a new translation that eliminates the
		 * current trivial solution from the set of possible solutions. The
		 * latter has the effect of forcing either the translator or the solver
		 * to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 * 
		 * @requires this.translation != null
		 * @ensures this.translation is modified to eliminate the current
		 *          trivial solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextTrivialSolution() {
			throw new UnsupportedOperationException("Trivial target-oriented next not yet supported.");
		}

		/**
		 * Calculates the next TO solutions with weights.
		 * 
		 * @param i
		 *            the TO mode
		 * @param weights
		 *            the signature weights
		 */
		// [HASLab]
		public Solution next(Map<String, Integer> weights) {
			if (opt.targetoriented()) {
				if (!(opt.solver().instance() instanceof TargetSATSolver))
					throw new AbortedException("Selected solver (" + opt.solver()
							+ ") does not have support for targets.");
				if (weights != null) {
					if (!(opt.solver().instance() instanceof WTargetSATSolver))
						throw new AbortedException("Selected solver (" + opt.solver()
								+ ") does not have support for targets with weights.");
				}
			}
			this.weights = weights;
			return next();
		}

	}

}