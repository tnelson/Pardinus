/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
package kodkod.cli;

import java.util.*;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.*;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

import org.parboiled.errors.ActionException;

import static kodkod.cli.KodkodFactory.setOf;
import static kodkod.cli.KodkodFactory.tuple;

/**
 * Provides a set of actions invoked by the {@link KodkodParser Kodkod parser}
 * to specify and solve relational satisfiability problems. A
 * {@link KodkodProblem} instance represents either a complete or an incremental
 * specification of a Kodkod problem.
 *
 * <p>
 * A complete specification consists of {@link Options}, {@link Bounds}, a set
 * of asserted {@link Formula formulas}, and a problem {@link StringDefEnv
 * definition environment}. It represents a stand-alone problem description in
 * which each asserted formulas refers to the relations bound the problem's own
 * {@link Bounds} instance. Complete specifications are solved with a
 * {@link Solver standard solver}.
 * </p>
 *
 * <p>
 * An incremental specification also consists of {@link Options},
 * {@link Bounds}, a set of asserted {@link Formula formulas}, and a problem
 * {@link DefEnv definition environment}. But unlike a complete specification,
 * an incremental specification is composed of a sequence of partial
 * specifications. The first specification in this sequence is a stand-alone
 * problem description. But each subsequent specification may assert formulas
 * that refer to relations that are not bound in its own {@link Bounds}
 * instance, as long as they appear in previously specified {@link Bounds}.
 * </p>
 *
 * <p>
 * Incrementally specified problems are solved with an {@link IncrementalSolver
 * incremental solver}, and the sequence of partial specification describing
 * such a problem must satisfy the requirements imposed by the incremental
 * solving API. For example, the {@link Options}, {@link #declareUniverse(int)
 * universe} and {@link #declareInts(List) integer bounds} can only be
 * configured/declared in the initial specification; they may not be extended or
 * modified in any way by subsequent partial specifications. The
 * {@link IncrementalSolver} documentation describes the remaining restrictions
 * in detail.
 * </p>
 *
 * <p>
 * All specification action methods return <code>true</code> on success and
 * throw an {@link ActionException action exception} on failure. References to a
 * problem specification {@code p} should be discarded by client code after a
 * reference to a new specification has been obtained from {@code p} by calling
 * {@link #extend()} or {@link #clear()}.
 * </p>
 *
 * @specfield prev: lone {@link KodkodProblem}
 * @specfield options: {@link Options}
 * @specfield bounds: lone {@link Bounds}
 * @specfield asserts: set {@link Formula} // top-level formulas
 * @specfield env: {@link StringDefEnv} // definitions for this problem
 * @specfield maxSolutions: long // maximum number of solutions that may be
 *            produced for this problem
 *
 * @invariant one this.*prev.options && one this.*prev.bounds.universe
 * @invariant some this.prev => no this.intBound && (no this.relations &
 *            this.^prev.bounds.relations) && this.partial() &&
 *            this.incremental()
 * @invariant all p: this.^prev | p.incremental()
 * @invariant (this.*prev.asserts.*components & Relation) in
 *            this.*prev.bounds.relations
 * @invariant this.*prev.bounds.relations = this.env['r']
 *
 * @author Emina Torlak
 */
public abstract class KodkodProblem {
	private long buildTimeMillis = -1, coreTimeMillis = -1, maxSolutions = 1;
	protected ExtendedOptions options; // allow subclasses to manipulate
	private final StringDefEnv env;
	private final List<Formula> asserts;
	private PardinusBounds bounds;

	final String id;

	/**
	 * Creates a partial problem with the given state.
	 * 
	 * @requires prev.incremental()
	 * @ensures this.bounds' = bounds && no this.asserts' && this.env' = env &&
	 *          this.options' = options && this.maxSolutions' = maxSolutions
	 */
	private KodkodProblem(StringDefEnv env, PardinusBounds bounds, ExtendedOptions options, long maxSolutions, String id) {
		this.env = env;
		this.bounds = bounds;
		this.options = options;

		// TODO: hack, should clean up
		// The problem is that the super() constructor of the subclasses
		// needs to be called before the subclass constructor can set
		// these options itself. Perhaps subclassing is wrong idea here
		if(isTargetOriented()) options().setRunTarget(true);
		if(isTemporal()) options().setRunTemporal(true);

		// this.options.setSymmetryBreaking(20);
		this.asserts = new ArrayList<>();
		this.maxSolutions = maxSolutions;
		this.id = id;
	}

	/**
	 * Creates a problem with {@link KodkodFactory#baseOptions()}.
	 * 
	 * @ensures this(new DefEnv(), null, KodkodFactory.baseOptions(), 1)
	 */
	private KodkodProblem(String id) {
		this(new StringDefEnv(), null, KodkodFactory.baseOptions(), 1, id);
	}

	/**
	 * Returns an empty {@link KodkodProblem} that can be used to construct a
	 * complete, stand-alone specification of a new relational satisfiability
	 * problem. The specification will be initialized with
	 * {@link KodkodFactory#baseOptions()}. with the given options.
	 * 
	 * @return some p: {@link KodkodProblem} | no p.prev && !p.incremental() &&
	 *         p.options = KodkodFactory.baseOptions() && no p.bounds && no
	 *         p.asserts && p.env = new StringDefEnv() && p.maxSolutions = 1
	 */
	//public static KodkodProblem complete() {
//		return new KodkodProblem.Complete();
//	}

	/**
	 * Returns an empty {@link KodkodProblem} that can be used to construct the
	 * first (stand-alone) component of an incremental specification of a new
	 * relational satisfiability problem. The specification will be initialized with
	 * {@link KodkodFactory#baseOptions()}.
	 * 
	 * @return some p: {@link KodkodProblem} | no p.prev && p.incremental() &&
	 *         p.options = KodkodFactory.baseOptions() && no p.bounds && no
	 *         p.asserts && p.env = new StringDefEnv() && p.maxSolutions = 1
	 */
//	public static KodkodProblem incremental() {
//		return new KodkodProblem.Incremental();
//	}

	/**
	 * Returns a new Stepper problem!
	 */
	public static KodkodProblem stepper(String id) {
		//System.exit(200);
		//System.out.println("stepper:"+Logger.getGlobal());
		//System.err.println("stepper:"+Logger.getGlobal());
		return new KodkodProblem.Stepper(id);
	}

	/**
	 * Returns a new Target Oriented problem
	 */
	public static KodkodProblem targetOriented(String id) {
		return new KodkodProblem.Stepper.TargetOriented(id);
	}

	/**
	 * Returns a new Target Oriented problem!
	 */
	public static KodkodProblem temporal(String id) {
		return new KodkodProblem.Stepper.Temporal(id);
	}

	/**
	 * Returns an empty partial {@link KodkodProblem} instance that can be used to
	 * extend the incremental specification composed of the sequence of problems
	 * ending with this {@link KodkodProblem}. Throws {@link ActionException} if
	 * this is not an {@link #incremental() incremental} specification.
	 * 
	 * @requires some this.bounds && this.incremental()
	 * @return some p: {@link KodkodProblem} | p.prev = this && p.incremental() &&
	 *         p.options = this.options && p.bounds = new
	 *         Bounds(this.bounds.universe) && no p.asserts && no p.env.parent &&
	 *         p.env.defs = this.env.defs && p.maxSolutions = this.maxSolutions
	 */
	public abstract KodkodProblem extend();

	/**
	 * Returns an empty {@link KodkodProblem} that can be used to construct a
	 * stand-alone specification of a new relational satisfiability problem. The
	 * returned instance is like this problem in the following sense: it is
	 * incremental iff this is incremental; it is initialized with
	 * {@code this.options}; and it has {@code this.maxSolutions} as its limit on
	 * the maximum number of solutions.
	 * 
	 * @return some p: {@link KodkodProblem} | no p.prev && (p.incremental() iff
	 *         prototype.incremental()) && p.options = prototype.options &&
	 *         p.maxSolutions = prototype.maxSolutions && no p.bounds && no
	 *         p.asserts && p.env = new StringDefEnv()
	 */
	public abstract KodkodProblem clear(KodkodOutput out);

	/**
	 * Solves this and outputs the resulting solution(s) to the given {@code out}.
	 * The number of produced solutions is bound above by {@code this.maxSolutions}.
	 * After solving the problem, this method returns a new empty
	 * {@link KodkodProblem} that can be used either to extend the specification
	 * comprising this problem with additional constraints, if this is an
	 * incremental {@link KodkodProblem}, or to construct a new complete
	 * specification otherwise.
	 * 
	 * @requires some this.problem.bounds
	 * @ensures some S: set SOLUTIONS(Formula.and(this.*prev.asserts),
	 *          this.*prev.bounds, this.options) | (all s: S | out.writeSolution(s,
	 *          this) ) && 0 < #S <= this.maxSolutions
	 * @return !this.isIncremental() => this.clear() else this.extend()
	 * @throws ActionException any solving pre-conditions are violated
	 **/
	public abstract KodkodProblem solve(KodkodOutput out, String params);

	// TN TODO: shouldn't be a String, but need to prototype multiple exploration types before better representation

	// public final KodkodProblem solveNext(KodkodOutput out){
	// if (!KodkodServer.lastModelAvailable){
	// out.writeCore(null, null);
	// } else if (!(KodkodServer.lastModel.hasNext())){
	// out.writeCore(null, null);
	// } else {
	// Solution sol = KodkodServer.lastModel.next();
	// if (sol.sat()){
	// out.writeInstance(sol.instance(), KodkodServer.lastRDefs);
	// } else {
	// out.writeCore(null, null);
	// }
	// }
	// return clear();
	// }

	/**
	 * Returns the problem definitions environment. The relation ('r') register in
	 * the returned environment should not be modified by client code, other than
	 * through the {@link #declareRelation(String, TupleSet, TupleSet)} method. The
	 * variable ('v') register of the problem environment is unmodifiable.
	 * 
	 * @return this.env
	 */
	public final StringDefEnv env() {
		return env;
	}

	/**
	 * Returns {@code this.bounds}. The bounds should not be modified by client code
	 * during the lifetime of this {@link KodkodProblem} except through the
	 * {@link #declareInts(List)} or
	 * {@link #declareRelation(int, TupleSet, TupleSet)} methods.
	 * 
	 * @return this.bounds
	 */
	public final PardinusBounds bounds() {
		return bounds;
	}

	/**
	 * Returns the union of all bounds in {@code this.*prev}.
	 * 
	 * @return let prevs = this.*prev.bounds | some b: Bounds | b.universe =
	 *         prevs.universe && b.intBound = prevs.intBound && b.lowerBound =
	 *         prevs.lowerBound && b.upperBound = prevs.upperBound
	 */
	public Bounds allBounds() {
		return bounds;
	}

	/**
	 * Returns {@code this.options}. The options should not be modified by client
	 * code during the lifetime of this {@link KodkodProblem} except through the
	 * {@link #configureOptions(Options)} method.
	 * 
	 * @return this.options
	 */
	public final ExtendedOptions options() {
		return options;
	}

	/**
	 * Returns the conjunction of {@code this.asserts}.
	 * 
	 * @return Formula.and(this.asserts)
	 */
	public final Formula asserts() {
		return Formula.and(asserts);
	}

	/**
	 * Returns the time in milliseconds that had elapsed between the calls to
	 * {@link #startBuild()} and {@link #endBuild()} on this instance. If the calls
	 * were not made, or if they were not made as specified by {@link #startBuild()}
	 * and {@link #endBuild()}, the value returned by this method is undefined.
	 * 
	 * @return problem building (parsing) time, in milliseconds
	 */
	public final long buildTimeMillis() {
		return buildTimeMillis;
	}

	/**
	 * Returns the time in milliseconds taken to minimize the unsat core during the
	 * last call to {@link #solve(KodkodOutput)} on this instance. If no call to
	 * solve was made, or if it was made and no core minimization was performed, the
	 * value returned by this method is undefined.
	 * 
	 * @return core extraction and minimization time, in milliseconds
	 */
	public final long coreTimeMillis() {
		return coreTimeMillis;
	}

	/**
	 * Returns true iff this is a (partial or stand-alone) component of an
	 * incremental specification.
	 * 
	 * @return true iff this is a (partial or stand-alone) component of an
	 *         incremental specification.
	 */
	public abstract boolean isIncremental();

	/**
	 * Returns true iff this is a partial specification.
	 * 
	 * @return some this.prev
	 */
	public abstract boolean isPartial();

	/**
	 * Returns true iff this is a Stepper specification (solved or unsolved).
	 * 
	 * @return some this.prev
	 */
	public boolean isStepper() {
		return false;
	}

	/**
	 * Returns true iff this is a Target Oriented specification (solved or
	 * unsolved).
	 * 
	 * @return some this.prev
	 */
	public boolean isTargetOriented() {
		return false;
	}

	public boolean isTemporal() {
		return false;
	}

	/**
	 * Returns true iff this is a solved Stepper specification.
	 * 
	 * @return some this.prev
	 */
	public boolean isSolved() {
		return false;
	}

	/**
	 * An action used to inform this problem instance that its state is about to be
	 * populated. This method assumes, but does not check, that no other action
	 * methods have yet been called on this problem instance. This method should be
	 * called exactly once, prior to all other actions being performed.
	 * 
	 * @return true
	 */
	final boolean startBuild() {
		buildTimeMillis = System.currentTimeMillis();
		return true;
	}

	/**
	 * An action used to inform a this problem instance that its state has been
	 * populated. This method assumes, but does not check, that no other action
	 * methods will ever be called on this problem instance. This method should be
	 * called exactly once, after all other actions have been performed.
	 * 
	 * @return true
	 */
	final boolean endBuild() {
		buildTimeMillis = System.currentTimeMillis() - buildTimeMillis;
		return true;
	}

	/**
	 * Returns {@code this.maxSolutions}.
	 * 
	 * @return this.maxSolutions
	 */
	public final long maxSolutions() {
		return maxSolutions;
	}

	/**
	 * Sets {@code this.maxSolutions} to the given value.
	 * 
	 * @requires maxSolutions > 0
	 * @return true
	 */
	final boolean setMaxSolutions(long maxSolutions) {
		if (maxSolutions < 1)
			throw new ActionException("Expected maxSolutions > 0, given " + maxSolutions);
		this.maxSolutions = maxSolutions;
		return true;
	}

	/**
	 * Sets the logging level of {@code this.options.reporter.logger} to the
	 * specified value. Calling this method on a partial {@link KodkodProblem} will
	 * result in an {@link ActionException}.
	 * 
	 * @requires no this.prev
	 * @ensures this.options.reporter.logger.level' = level
	 */
	boolean setVerbosity(Level level) {
		final Logger logger = ((KodkodReporter) options.reporter()).logger();
		logger.setLevel(level);
		for (Handler h : logger.getHandlers()) {
			h.setLevel(level);
		}
		return true;
	}

	/**
	 * Sets {@code this.options.bitwidth} to the specified value. Calling this
	 * method on a partial {@link KodkodProblem} will result in an
	 * {@link ActionException}.
	 * 
	 * @requires no this.prev
	 * @ensures this.options.bitwidth' = bitwidth
	 */
	boolean setBitwidth(int bitwidth) {
		try {
			options.setBitwidth(bitwidth);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	boolean setSB(int sb) {
		try {
			options.setSymmetryBreaking(sb);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	boolean setSkolemDepth(int sd) {
		try {
			options.setSkolemDepth(sd);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	boolean setCoreGranularity(int gran) {
		try {
			options.setCoreGranularity(gran);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	boolean setLogTranslation(int lt) {
		try {
			options.setLogTranslation(lt);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	/**
	 * Sets {@code this.options.solver} to the specified solver factory. Calling
	 * this method on a partial {@link KodkodProblem} will result in an
	 * {@link ActionException}. An {@link ActionException} will also be thrown if
	 * this method is called with a non-incremental {@link SATFactory} on an
	 * incremental problem specification.
	 * 
	 * @requires no this.prev
	 * @ensures this.options.solver' = solver Changed for Pardinus
	 */
	boolean setSolver(SATFactory solver) {
		if (SATFactory.available(solver)) {
			options.setSolver(solver);
			return true;
		} else {
			throw new ActionException(solver.toString() + " is not available on this system. Searched "
					+ System.getProperty("java.library.path"));
		}
	}
	boolean setSolver(KodkodOutput out, SATFactory solver) {
		//out.writeInfo("configuring solver");
		return setSolver(solver);
	}

	/**
	 * Modifies {@code this.options} so as to enable or disable minimal core
	 * extraction. Calling this method on a partial {@link KodkodProblem} will
	 * result in an {@link ActionException}. An {@link ActionException} will also be
	 * thrown if this method is called with <code>true</code> on an incremental
	 * problem specification.
	 * 
	 * @requires no this.prev
	 * @ensures enable => (this.options.setLogTranslation(1) &&
	 *          this.options.setCoreGranularity(0) &&
	 *          this.ooptions.setSatSolver(SATFactory.MiniSatProver)) else
	 *          (this.options.setLogTranslation(0) &&
	 *          this.options.setCoreGranularity(0))
	 **/
	// Just set solver, LT, and CG separately.
	@Deprecated
	boolean setCoreExtraction(boolean enable) {
		try {
			if (enable) {
				if (!SATFactory.available(SATFactory.MiniSatProver)) {
					throw new ActionException(
							"Cannot enable core extraction since no proof-logging solver is available on this system.");
				}
				options.setLogTranslation(1);
				options.setCoreGranularity(0);
				// Changed for Pardinus
				options.setSolver(SATFactory.MiniSatProver);
			} else {
				options.setLogTranslation(0);
				options.setCoreGranularity(0);
			}
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	/**
	 * Sets {@code this.bounds} to an empty {@link Bounds} over a freshly created
	 * universe of the given size. The created universe consists of {@link Integer
	 * integers} in the range {@code [0..size)}. Calling this method after bounds
	 * have already been defined will result in an {@link ActionException}.
	 * 
	 * @requires no this.prev
	 * @requires no this.bounds
	 * @ensures this.bounds'.universe.atoms = [0..size)<:iden
	 * @ensures no this.bounds'.intBound && no this.bounds'.lowerBound && no
	 *          this.bounds'.upperBound
	 */
	final boolean declareUniverse(int size) {
		if (bounds != null)
			throw new ActionException("Universe already defined.");
		try {
			final List<Integer> atoms = new ArrayList<Integer>(size);
			for (int i = 0; i < size; i++) {
				atoms.add(i);
				env.def('a', Integer.toString(i), Relation.unary("atom " + i));
				// Note: Pardinus in temporal mode will add "Time" atoms.
				//  these will generally appear at the beginning of the indexing
				//  and thus tuple.atomIndex cannot be relied upon as a ref. to atom name.
				//  Instead, recognize new atoms by their absence in the 'a' registry keys
			}
			final Universe universe = new Universe(atoms);
			bounds = new PardinusBounds(universe);
		} catch (IllegalArgumentException ex) {

			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	/**
	 * Sets the interpretation of integer atoms in {@code this.bounds} by performing
	 * {@code this.bounds.boundExactly(ints.get(i), ints.get(i+1))} on each even
	 * {@code i} in {@code [0..ints.size())}. Assumes that no integers have been
	 * already bound in {@code this.bounds}. Calling this method after ints have
	 * already been defined, or calling it on a partial {@link KodkodProblem}, will
	 * result in an {@link ActionException}.
	 * 
	 * @requires no this.prev
	 * @requires some this.bounds
	 * @requires no bounds.ints()
	 * @requires ints.size() % 2 = 0
	 * @requires all i: [0..ints.size()) | i % 2 = 1 => ints.get(i) in
	 *           bounds.universe.atoms[int]
	 * @ensures all i: [0..ints.size()) | i % 2 = 0 =>
	 *          this.bounds.boundExactly(ints.get(i),
	 *          this.bounds.universe.factory.setOf(ints.get(i+1))
	 */
	boolean declareInts(List<Integer> ints) {
		if (!bounds.intBounds().isEmpty())
			throw new ActionException("Integer bounds already defined.");
		try {
			final Universe univ = bounds.universe();
			final TupleFactory f = univ.factory();
			final IntSet intAtomIndices = Ints.bestSet(univ.size());
			for (int idx = 0, size = ints.size(); idx < size; idx += 2) {
				final int i = ints.get(idx);
				final Integer atom = ints.get(idx + 1);

				final TupleSet ibound = bounds.exactBound(i);
				if (ibound != null) {
					throw new ActionException("Cannot bind the integer " + i + "to atom " + atom
							+ " since it is already bound to atom " + ibound.indexView().min() + ".");
				}
				if (!intAtomIndices.add(univ.index(atom)))
					throw new ActionException("Cannot bind the integer " + i + " as atom " + atom
							+ " since a different integer is already bound to this atom.");

				bounds.boundExactly(i, f.setOf(atom));
			}
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}

		return true;
	}

	/**
	 * Creates a set of relations with the given indices, adds them to
	 * {@code this.env.defs['r']}, and bounds them in {@code this.bounds} using the
	 * given lower/upper bounds.
	 * 
	 * @requires no this.env.defs['r'].def[idxs[int]]
	 * @requires #idxs[int] = idxs.size()
	 * @requires lower.arity = upper.arity
	 * @requires some this.bounds
	 * @ensures let R = this.bounds.relations' - this.bounds.relations | #R =
	 *          idxs.size() && (all idx: idxs[int] | some r: R |
	 *          r.name.equals("r"+idx)) && r.arity() = lower.arity &&
	 *          this.bounds.lowerBound'[r] = lower && this.bounds.upperBound'[r] =
	 *          upper && this.env.def('r', idx, r))
	 */
	final boolean declareRelations(List<String> names, TupleSet lower, TupleSet upper) {
		try {
			for (String name : names) {
				final Relation r = Relation.nary(name, lower.arity());
				env.def('r', name, r);
				bounds.bound(r, lower, upper);
				declaredRelation(r, lower, upper);
			}
		} catch (RuntimeException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	// varRelation
	final boolean declareVarRelations(List<String> names, TupleSet lower, TupleSet upper) {
		try {
			for (String name : names) {
				// final Relation r = Relation.nary(name, lower.arity());
				final Relation x = Relation.variable(name, lower.arity());
				env.def('x', name, x);
				bounds.bound(x, lower, upper);
				declaredRelation(x, lower, upper);
			}
		} catch (RuntimeException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	/**
	 * Used to allow forced references to concrete atoms in expressions; useful for concrete test cases without chains
	 * of quantifiers to build characteristic formulas.
	 * */
	final boolean boundForcedAtomIfNeeded(char varPrefix, String atom) {
		if(varPrefix != 'a') return true; // only try to register atom
		if(bounds == null) return true; // no bounds = in evaluator, atoms already registered

		Relation atomRelation = (Relation) env.defs('a').use(atom.toString());
//		Logger.getGlobal().severe("boundForcedAtomIfNeeded: atom="+atom+" " + atom.getClass()+"; atomRelation="+atomRelation);

		if(bounds.upperBound(atomRelation) == null) {
			Tuple tup = bounds.universe().factory().tuple(Integer.parseInt(atom));
			TupleSet ts = bounds.universe().factory().setOf(tup);
			bounds.bound(atomRelation, ts, ts);
		} // otherwise, already bounded
		return true;
	}

	boolean setTarget(List<Relation> rels, TupleSet tuple) {
		if (!this.isTargetOriented()) {
			throw new ActionException("Cannot set target for non-target oriented problem.");
		}

		try {
			for (Relation rel : rels) {
				bounds.setTarget(rel, tuple);
			}
		} catch (RuntimeException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	boolean setTargetType(KodkodOutput out, String target_type) {
		throw new ActionException("Cannot set target option for non-target oriented problem.");
	}

	/**
	 * Hook for subclasses to intercept relation creation calls. It is called by
	 * {@linkplain #declaredRelation(Relation, TupleSet, TupleSet)} whenever it adds
	 * a new relation to {@code this.bounds}. Does nothing by default.
	 */
	void declaredRelation(Relation r, TupleSet lower, TupleSet upper) {
	}

	// void declaredVarRelation(Relation x, TupleSet lower, TupleSet upper) { }

	/**
	 * Adds the given formula to {@code this.asserts}.
	 * 
	 * @return this.asserts.add(formula)
	 */
	final boolean assertFormula(Formula formula) {
		return asserts.add(formula);
	}

	/**
	 *
	 */
	boolean evaluate(kodkod.ast.Expression expression) {
		throw new ActionException("Can only evaluate for stepper problems.");
	}

	/**
	 *
	 */
	boolean evaluate(kodkod.ast.IntExpression expression) {
		throw new ActionException("Can only evaluate for stepper problems.");
	}

	/**
	 *
	 */
	boolean evaluate(Formula formula) {
		throw new ActionException("Can only evaluate for stepper problems.");
	}

	/**
	 * Prints the given solution for this problem to {@code out}, after first
	 * minimizing its core, if any.
	 * 
	 * @requires sol in SOLUTIONS(Formula.and(this.*prev.asserts),
	 *           this.*prev.bounds, this.options)
	 * @ensures some sol.proof => sol.proof.minimize(new RCEStrategy(sol.proof.log))
	 * @ensures out.print(sol, this)
	 */
	final void write(KodkodOutput out, Solution sol) {
		if (sol.proof() != null) { // core extraction was enabled
			coreTimeMillis = System.currentTimeMillis();
			sol.proof().minimize(new RCEStrategy(sol.proof().log()));
			coreTimeMillis = System.currentTimeMillis() - coreTimeMillis;
		}
		out.writeSolution(sol, this);
	}

	/**
	 * Prints at most {@code this.maxSolutions} solutions from the given iterator to
	 * {@code out}. The first solution is always printed, using
	 * {@link #print(Solution)}. If the first solution is SAT, then only subsequent
	 * SAT solutions are printed; the last, unsatisfiable, solution is discarded.
	 * 
	 * @requires (sols.first).*(sols.next) in
	 *           SOLUTIONS(Formula.and(this.*prev.asserts), this.*prev.bounds,
	 *           this.options)
	 * @ensures some last: (sols.first).*(sols.next) | let S = last.*~(sols.next) |
	 *          0 < #S <= this.maxSolutions && all s: S | this.output(out, sol)
	 **/
	final void write(KodkodOutput out, Iterator<Solution> sols) {
		Solution sol = sols.next();
		write(out, sol); // print the first solution
		if (sol.sat()) { // there has to be at least one more, possibly unsat, solution after the first
							// sat solution
			long atMost = maxSolutions;
			while (--atMost > 0 && (sol = sols.next()).sat()) { // don't print the last unsat solution
				write(out, sol);
			}
		}
	}

	final void writeUnsat(KodkodOutput out, Solution sol) {
		out.writeUnsat(sol, this);
	}

	public boolean setMaxTraceLength(Integer popInt)
	{
		try {
			options.setMaxTraceLength(popInt);
			options.setRunTemporal(true);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}
	public boolean setMinTraceLength(Integer popInt)
	{
		try {
			options.setMinTraceLength(popInt);
			options.setRunTemporal(true);
		} catch (IllegalArgumentException ex) {
			throw new ActionException(ex.getMessage(), ex); // wrap
		}
		return true;
	}

	String coreMinimization = "none";
	public boolean setCoreMinimization(String coreMinimization) {
		this.coreMinimization = coreMinimization;
		return true;
	}


	// The other problem classes have good reason to return new objects; they need to clear the bounds and asserts.
	// However, for Stepper, we only need to return new objects when we transition to a solved stepper.
	// A solved stepper can return itself.
	private static class Stepper extends KodkodProblem {
		private PardinusSolver solver;
		private boolean issolved = false;
		private Solution lastSol;
		private int iteration = -1;
		private boolean unsat = false;
		private Evaluator evaluator = null;
		private PardinusBounds bounds = null;

		// Used to print new solutions from the first solved model.
		private Explorer<Solution> solutions;

		Stepper(String id) {
			// Do not create the solver yet. Options have yet to be set!
			//this.solver = new PardinusSolver(super.options);
			super(id);
			super.maxSolutions = -1; // maxSolutions has no meaning for Steppers.
		}

		// makes a solved stepper with the given solutions.
		private Stepper(Stepper prototype, Explorer<Solution> solutions, String id) {
			super(prototype.env(), null, null, -1, id);
			assert (solutions != null);
			this.solver = null;
			this.issolved = true;
			this.solutions = solutions;
			this.options = prototype.options();
			this.bounds = prototype.bounds();
			this.coreMinimization = prototype.coreMinimization;
			assert (this.iteration == -1);
		}

		public boolean isIncremental() {
			return false;
		}

		public boolean isPartial() {
			return false;
		}

		public boolean isStepper() {
			return true;
		}

		public boolean isTargetOriented() {
			return false;
		}

		public boolean isSolved() {
			return issolved;
		}

		public KodkodProblem extend() {
			throw new ActionException("Cannot extend a non-incremental specification.");
		}

		public KodkodProblem clear(KodkodOutput out) {
			if (solver != null)
				solver.free();
			out.writeInfo("closing solver state for <"+this.id+">");
			return new Stepper(this.id);
		}

		public KodkodProblem solve(KodkodOutput out, String params) {
			//out.writeInfo("stepper solving; hash="+this.hashCode()+"; solved="+isSolved());
			if(this.solver == null) {
				// Create solver only when needed; at this point all options should be set.
				this.solver = new PardinusSolver(super.options);
				//out.writeInfo("stepper solver created");
			}

			//System.err.println("solver is pardinus: "+solver.solver.getClass());
			if (isSolved()) {
				out.writeInfo("stepper solving:  unsat="+unsat+"; iteration="+this.iteration);
				// TODO: if this assertion fails, we get a cryptic error from the parser without context
				//assert (this.iteration >= 0);
				// The assertion is also in error. We start at iteration -1.
				this.iteration++;


				if (this.unsat) {
					assert (lastSol != null);
					writeUnsat(out, lastSol);
					return this;
				}

				// TODO: again shouldn't be a string, but need to experiment with enough exploration variants to improve
				// Ideally, we'd have a factory that would produce a strategy
				// Don't try to use the temporal next buttons if they are unavailable
				boolean hasNext = false;
				switch(params) {
					case "C": hasNext = this.isTemporal() ? solutions.hasNextC() : solutions.hasNext(); break;
					case "P": hasNext = this.isTemporal() ? solutions.hasNextP() : solutions.hasNext(); break;
					default: hasNext = solutions.hasNext();
				}
				if (hasNext) {
					Solution sol;
					switch(params) {
						case "C": sol = this.isTemporal() ? solutions.nextC() : solutions.next(); break;
						case "P": sol = this.isTemporal() ? solutions.nextP() : solutions.next(); break;
						default: sol = solutions.next();
					}

					// If our first solution is also our last, then the spec
					// is unsatisfiable, and we say so.
					if ((this.iteration == 0) && !(solutions.hasNext())) {
						this.unsat = true;
						lastSol = sol;
						writeUnsat(out, lastSol);
						return this;
					} else {
						if(sol.sat()) {
							// Add helper relations to instance
							Instance instance = sol.instance().clone();
							for (String atom : env().keys('a')) {
								// need to use instance.universe() here, not bounds.universe()
								if(!(instance.relations().contains(env().use('a', atom)))) {
									instance.add(env().use('a', atom),
											setOf(tuple(instance.universe().factory(), Arrays.asList(Integer.parseInt(atom)))));
								}
							}
							evaluator = new Evaluator(instance, options());
						} else {
							evaluator = null;
						}

						write(out, sol);
						lastSol = sol;
						return this;
					}
				}

				// If we finished our list of solutions, we just keep repeating the last
				// solutions found, which will be no-more-instances.
				else {
					assert (lastSol != null);
					write(out, lastSol);
					return this;
				}
			} // end if is solved

			try {
				// In case the solver is not incremental, but Stepper is being used
				//   (e.g. for Temporal or Target-oriented mode), mock enumeration.
				if(options.solver().incremental()) {
					this.solutions = solver.solveAll(asserts(), bounds());
				} else {
					this.solutions = new OneSolutionIterator(solver.solve(asserts(), bounds()));
				}
				this.issolved = true;
				out.writeInfo("stepper solving: initial solve call with params: "+params+" finished.");
				return this.solve(out, params);
			} catch (RuntimeException ex) {
				throw new ActionException(ex.getMessage(), ex);
			}
		}

		public boolean evaluate(kodkod.ast.Expression expression) {
			//Logger.getGlobal().severe("Evaluating " + expression);
			if(evaluator == null) {
				System.out.println("(unsat)");
				return true;
			}

			//TupleSet ts = null;

			TupleSet ts = evaluator.evaluate(expression);
			// Kludge here to write the issue to file
			// TODO should move this to happen on any exception
			// Keeping for reference
			/*try {
				ts = evaluator.evaluate(expression);
			} catch(UnboundLeafException e) {
				java.awt.Toolkit.getDefaultToolkit().beep();
				try {
					File f = File.createTempFile("baz", "foo");
					PrintWriter pr = new PrintWriter(f);
					e.printStackTrace(pr);
					pr.println();
					pr.println(evaluator.instance() instanceof TemporalInstance);
					//pr.println(((TemporalInstance)evaluator.instance()).state(0));
					//pr.println(((TemporalInstance)evaluator.instance()).state(0).relations().contains(expression));
					//pr.println(((TemporalInstance)evaluator.instance()).relations().contains(expression));
					pr.flush();
					pr.close();
				} catch (Exception e2) { }
			}*/

			StringBuilder str = new StringBuilder();
			str.append("{");
			for (Tuple t : ts) {
				str.append("(");
				// Previously used atomIndex, but now use atom
				// to allow for hidden atoms added by Electrum
				str.append(t.atom(0));
				for (int idx = 1; idx < ts.arity(); idx++) {
					str.append(" ").append(t.atom(idx));
				}
				str.append(")");
			}
			str.append("}");
			System.out.println("(evaluated :expression " + str + ")");

			return true;
		}

		public boolean evaluate(kodkod.ast.IntExpression expression) {
			if(evaluator == null) {
				System.out.println("(unsat)");
				return true;
			}
			System.out.println("(evaluated :int-expression " + evaluator.evaluate(expression) + ")");
			return true;
		}

		public boolean evaluate(Formula formula) {
			if(evaluator == null) {
				System.out.println("(unsat)");
				return true;
			}
			System.out.println("(evaluated :formula " + evaluator.evaluate(formula) + ")");
			return true;
		}

		private static final class TargetOriented extends Stepper {

			String target_type;
			boolean initialized = false;
			enum FLIP {yes, no, custom};
			FLIP flip_target = FLIP.no;

			boolean setTargetType(KodkodOutput out, String target_type) {
				if (initialized)
					throw new IllegalStateException("Target type was already set");
				this.initialized = true;
				out.writeInfo("set target type: "+target_type);

				this.target_type = target_type;
				options().setRunTarget(true);

				// These names are likely to change with further dev.
				// TODO: enum?
				// More names also need adding to Parser
				switch (target_type) {
					case "far_retarget":
						flip_target = FLIP.yes;
						break; // default retargeting
					case "close_retarget":
						flip_target = FLIP.no;
						break; // default retargeting

					case "far":
						flip_target = FLIP.yes;
						// NOTE NO BREAK -- fall through
					case "close":
						// Fix so that Pardinus doesn't move target around.
						options().setRetargeter(new Retargeter() {
							@Override
							public void retarget(Translation transl) {
							}
						});
						break;

					case "cover":
						flip_target = FLIP.custom;
						options().setRetargeter(new Retargeter() {
							boolean firstInstance = true;

							@Override
							public void retarget(Translation transl) {
								assert (transl.cnf() instanceof TargetSATSolver);
								TargetSATSolver tcnf = (TargetSATSolver) transl.cnf();
								assert (transl.options() instanceof ExtendedOptions);

								if (firstInstance) {
									tcnf.clearTargets(); // stop targeting initial instance
								}
								firstInstance = false;

								// Anti-target the current instance
								// Crucially, do not clear prior targets, since we want
								//   to build up a field of pressure away from instances seen
								for (int i = 1; i <= transl.numPrimaryVariables(); i++) {
									int tgt = tcnf.valueOf(i) ? -i : i;
									tcnf.addTarget(tgt);
								}
							}
						});
						break;
					default:
						throw new ActionException("Bad choice for target type: " + target_type);
				}

				return true;
			}

			TargetOriented(String id) {
				super(id);
				initialized = false;

				// Unnecessary?
				// options().setConfigOptions(options());
			}

			@Override
			public boolean isTargetOriented() {
				return true;
			}

			@Override
			public KodkodProblem solve(KodkodOutput out, String params) {
				// Invert the initial target if this is one of the
				// two "FAR" modes (with or without retargeting per result)
				if (!isSolved() && flip_target == FLIP.yes) {
					PardinusBounds pb = bounds();

					for (Relation rel : pb.targets().keySet()) {
						TupleSet tuples = pb.upperBound(rel).clone();
						tuples.removeAll(pb.targets().get(rel));
						tuples.addAll(pb.lowerBound(rel).clone());
						pb.setTarget(rel, tuples);
					}
				}

				return super.solve(out, params);
			}
		}

		private static final class Temporal extends Stepper {

			Temporal(String id) {
				super(id);
				// trace lengths configured at parse time
				options().setRunTemporal(true);

				// Unnecessary?
				// options().setConfigOptions(options());
			}

			@Override
			public boolean isTemporal() {
				return true;
			}
		}
	}

///**
//	 * Implements a complete specification of a Kodkod problem.
//	 *
//	 * @author Emina Torlak
//	 */
//	private static final class Complete extends KodkodProblem {
//		private final Solver solver;
//
//		Complete() {
//			this.solver = new Solver(super.options);
//		}
//
//		Complete(Complete prototype) {
//			super(new StringDefEnv(), null, prototype.options(), prototype.maxSolutions());
//			this.solver = prototype.solver;
//		}
//
//		public boolean isIncremental() {
//			return false;
//		}
//
//		public boolean isPartial() {
//			return false;
//		}
//
//		public boolean isStepper() {
//			return false;
//		}
//
//		public boolean isTargetOriented() {
//			return false;
//		}
//
//		public KodkodProblem extend() {
//			throw new ActionException("Cannot extend a non-incremental specification.");
//		}
//
//		public KodkodProblem clear(KodkodOutput out) {
//			return new Complete(this);
//		}
//
//		public KodkodProblem solve(KodkodOutput out, String paramsIgnored) {
//			try {
//				if (maxSolutions() == 1) {
//					write(out, solver.solve(asserts(), bounds()));
//				} else {
//					write(out, solver.solveAll(asserts(), bounds()));
//				}
//				return clear(out);
//			} catch (RuntimeException ex) {
//				throw new ActionException(ex.getMessage(), ex);
//			}
//		}
//	}

//	/**
//	 * Enforces options configuration restrictions for incremental specifications.
//	 *
//	 * @author Emina Torlak
//	 */
//	private static class Incremental extends KodkodProblem {
//		IncrementalSolver solver = null;
//
//		Incremental() {
//		}
//
//		Incremental(StringDefEnv env, PardinusBounds bounds, ExtendedOptions options, long maxSolutions,
//				IncrementalSolver solver) {
//			super(env, bounds, options, maxSolutions);
//			this.solver = solver;
//		}
//
//		public final boolean isIncremental() {
//			return true;
//		}
//
//		public boolean isPartial() {
//			return false;
//		}
//
//		public boolean isStepper() {
//			return false;
//		}
//
//		public boolean isTargetOriented() {
//			return false;
//		}
//
//		public final KodkodProblem extend() {
//			return new Partial(this);
//		}
//
//		public final KodkodProblem clear(KodkodOutput out) {
//			if (solver != null)
//				solver.free();
//			return new Incremental(new StringDefEnv(), null, options(), maxSolutions(), null);
//		}
//
//		public final KodkodProblem solve(KodkodOutput out, String paramsIgnored) {
//			try {
//				if (solver == null)
//					solver = IncrementalSolver.solver(options());
//				write(out, solver.solve(asserts(), bounds()));
//				KodkodServer.lastModel = null;
//				return extend();
//			} catch (RuntimeException ex) {
//				throw new ActionException(ex.getMessage(), ex);
//			}
//		}
//
//		boolean setCoreExtraction(boolean enable) {
//			if (enable)
//				throw new ActionException("Minimal unsat core extraction is not provided for incremental problems.");
//			return super.setCoreExtraction(enable);
//		}
//
//		// Changed for Pardinus
//		boolean setSolver(SATFactory solver) {
//			if (!solver.incremental())
//				throw new ActionException(
//						"Cannot use a non-incremental SAT solver (" + solver + ") for incremental solving.");
//			return super.setSolver(solver);
//		}
//
//	}

//	/**
//	 * Disables methods not supported for partial problem specifications.
//	 * @author Emina Torlak
//	 */
//	private static final class Partial extends KodkodProblem.Incremental {
//		//@SuppressWarnings("unchecked")
//		Partial(KodkodProblem.Incremental prev) {
//			super(prev.env(), new Bounds(prev.bounds().universe()), prev.options(), prev.maxSolutions(), prev.solver);
//		}
//		public final boolean isPartial() { return true; }
//		private final String cannot(String msg) {
//			return "Cannot " + msg + " of an incremental problem.  Use (clear) to start specifying a new problem.";
//		}
//		boolean setBitwidth(int bitwidth) { throw new ActionException(cannot("re-configure bitwidth")); }
//		boolean setSatSolver(SATFactory solver) { throw new ActionException(cannot("re-configure the solver")); }
//		boolean setCoreExtraction(boolean enable) { throw new ActionException(cannot("re-configure the core extraction behavior")); }
//		boolean declareInts(List<Integer> ints) { throw new ActionException(cannot("re-declare integer atoms in the universe of")); }
//	}

//	/**
//	 * Disables methods not supported for partial problem specifications.
//	 *
//	 * @author Emina Torlak
//	 */
//	private static final class Partial extends KodkodProblem.Incremental {
//		private final Bounds complete;
//
//		Partial(KodkodProblem.Incremental prev) {
//			super(prev.env(), new PardinusBounds(prev.bounds().universe()), prev.options(), prev.maxSolutions(),
//					prev.solver);
//			this.complete = prev.allBounds();
//		}
//
//		public final boolean isPartial() {
//			return true;
//		}
//
//		public boolean isStepper() {
//			return false;
//		}
//
//		public final Bounds allBounds() {
//			return complete;
//		}
//
//		void declaredRelation(Relation r, TupleSet lower, TupleSet upper) {
//			complete.bound(r, lower, upper);
//		}
//
//		// void declaredVarRelation(Relation x, TupleSet lower, TupleSet upper) {
//		// complete.bound(x, lower, upper); }
//
//		private final String cannot(String msg) {
//			return "Cannot " + msg + " of an incremental problem.  Use (clear) to start specifying a new problem.";
//		}
//
//		boolean setBitwidth(int bitwidth) {
//			throw new ActionException(cannot("re-configure bitwidth"));
//		}
//
//		// Changed for Pardinus
//		boolean setSolver(SATFactory solver) {
//			throw new ActionException(cannot("re-configure the solver"));
//		}
//
//		boolean setCoreExtraction(boolean enable) {
//			throw new ActionException(cannot("re-configure the core extraction behavior"));
//		}
//
//		boolean declareInts(List<Integer> ints) {
//			throw new ActionException(cannot("re-declare integer atoms in the universe of"));
//		}
//	}

	///////////////////////////////////////////////////////
	// Machinery to track source location of child formulas
	///////////////////////////////////////////////////////
	/** Record class to hold a mapping from parent Formula to child Formula.
	 *  Because "and(and(a, b))" produces and(a,b) we need to wrap to disambiguate.
	 */
    static class ParentIndex {
		final List<? extends Node> parent; // invar: size() = 1
		final int index;
		ParentIndex(List<? extends Node> parent, int index) {
			if(parent == null || parent.size() != 1)
				throw new IllegalArgumentException("To be wrapped, formula list must be a singleton list.");
			this.parent = parent;
			this.index = index;
		}
		@Override public String toString() { return "("+parent+","+index+")"; }
		@Override public int hashCode() { return Objects.hash(parent, index); }
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			ParentIndex that = (ParentIndex) o;
			return index == that.index && Objects.equals(parent, that.parent);
		}
	}
	Map<List<Node>, ParentIndex> parentIndexes = new HashMap<>();
	public void logNodeChild(Formula parent, int index, Node child, KodkodOutput out) {
		// Rely on structurally-identical children NOT being referentially equal.
		// However, Kodkod will optimize; e.g.: "and(and(a, b))" is built as and(a,b).
		// We cannot simply skip these, because the caller needs to rely on the structure
		// of the formula passed being represented in the child path. Therefore, if parent == child,
		// allow the duplication; we're wrapping per reference anyway.

		// For debugging only
		//System.out.println("Logging: "+child+"("+child.hashCode()+") ---> "+parent+","+index);
		//System.out.println("Logging: "+child+" ---> "+parent+","+index);

		List<Formula> parentWrapper = new ArrayList<>(1);
		List<Node> childWrapper = new ArrayList<>(1);
		parentWrapper.add(parent);
		childWrapper.add(child);
		parentIndexes.put(childWrapper, new ParentIndex(parentWrapper, index));
	}


} // end of KodkodProblem

/*
  Explorer to cover situation where only one solution can be enumerated
  by the solver, but Stepper problem is being used. Returning an
  UNSAT outcome after the first instance would be unsound. Instead,
  repeat the same instance if asked for another. This allows (e.g.)
  evaluator to function properly in this situation.
 */
class OneSolutionIterator implements Explorer<Solution> {

	private final Solution s;
	OneSolutionIterator(Solution s) {
		this.s = s;
	}

	@Override
	public Solution nextC() {
		return s;
	}

	@Override
	public Solution nextP() {
		return s;
	}

	@Override
	public Solution nextS(int state, int delta, Set<Relation> change) {
		return s;
	}

	@Override
	public boolean hasNextC() {
		return true;
	}

	@Override
	public boolean hasNextP() {
		return true;
	}

	@Override
	public boolean hasNext() {
		return true;
	}

	@Override
	public Solution next() {
		return s;
	}

}