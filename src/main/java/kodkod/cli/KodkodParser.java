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

import static kodkod.cli.KodkodFactory.acyclic;
import static kodkod.cli.KodkodFactory.add;
import static kodkod.cli.KodkodFactory.area;
import static kodkod.cli.KodkodFactory.cast;
import static kodkod.cli.KodkodFactory.compare;
import static kodkod.cli.KodkodFactory.compose;
import static kodkod.cli.KodkodFactory.compose_temp;
import static kodkod.cli.KodkodFactory.comprehension;
import static kodkod.cli.KodkodFactory.declareVariable;
import static kodkod.cli.KodkodFactory.ite;
import static kodkod.cli.KodkodFactory.level;
import static kodkod.cli.KodkodFactory.range;
import static kodkod.cli.KodkodFactory.setOf;
import static kodkod.cli.KodkodFactory.sum;
import static kodkod.cli.KodkodFactory.totalOrder;
import static kodkod.cli.KodkodFactory.tuple;
import static kodkod.cli.KodkodFactory.union;
import static kodkod.cli.KodkodFactory.valueOf;

import java.nio.charset.StandardCharsets;
import java.util.*;

import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.operator.ExprCastOperator;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntCastOperator;
import kodkod.ast.operator.IntCompOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.operator.TemporalOperator;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

import org.parboiled.BaseParser;
import org.parboiled.Rule;
import org.parboiled.annotations.Cached;
import org.parboiled.annotations.DontLabel;
import org.parboiled.annotations.MemoMismatches;
import org.parboiled.annotations.SuppressNode;
import org.parboiled.annotations.SuppressSubnodes;
import org.parboiled.errors.ActionException;
import org.parboiled.support.Var;
import org.parboiled.support.DefaultValueStack;

/**
 * A PEG parser for a concrete syntax for Kodkod inspired by Kodkodi and
 * SMT-LIB2. This parser does not support error recovery, since building the
 * problem requires state mutation that cannot be safely undone.
 *
 * @author Emina Torlak
 * @specfield problem: {@link KodkodProblem} // an empty KodkodProblem instance
 *            to be populated with the parsed specification
 * @specfield out: {@link KodkodOutput} // KodkodOutput instance to which
 *            solutions should be written
 */
public class KodkodParser extends BaseParser<Object> {
	final KodkodOutput out;

	/**
	 * Current problem being configured or invoked
	 */
	KodkodProblem currentProblem;
	/**
	 * ID of current problem
	 */
	String currentID = "";
	/**
	 * Index of all problems that are available
	 */
	Map<String, KodkodProblem> problems = new HashMap<>();
	/**
	 * All KodkodProblems created by this parser instance will have a specific type
	 */
	final KodkodServer.Feature type;


	/**
	 * If there is a KodkodOutput defined, write an info s-expression to it.
	 * @param info
	 */
	public void info(String info) {
		if(out != null)
			out.writeInfo(info);
	}

	/**
	 * Creates a parser that will output the result of any command executions to an instance of
	 * {@link StandardKodkodOutput}.
	 */
	public KodkodParser(KodkodServer.Feature type) {
		this(type, new StandardKodkodOutput());
	}

	/**
	 * Creates a {@link KodkodParser} that will output the result of any command executions to
	 * the given {@link KodkodOutput} object.
	 */
	public KodkodParser(KodkodServer.Feature type, KodkodOutput out) {
		this.out = out;
		this.type = type;
	}

	/**
	 * Returns the {@link KodkodProblem} (to be) populated by this parser.
	 *
	 * @return this.problem
	 */
	public KodkodProblem problem() {
		return currentProblem;
	}

	/**
	 * Sets {@code this.problem} to the given problem and returns true. Setting the
	 * problem to <code>null</code> causes this method to terminate the current JVM
	 * instance with a 0 exit code. So basically, when a solve() returns null,
	 * that's our cue to end the process.
	 *
	 * @return true
	 * @ensures this.problem' = problem
	 */
	public boolean setProblem(KodkodProblem problem) {
		if (problem == null)
			System.exit(0);
		this.currentProblem = problem;
		return true;
	}

	public Rule Problems() {
		return OneOrMore(Problem());
	}

	/**
	 * @return (Problem () IncrementalProblem()*)+ EOI
	 */
	public Rule IncrementalProblems() {
		return NOTHING;
	}

	/**
	 * @return (Problem () IncrementalProblem()*)+ EOI
	 */
	public Rule RestOfIncrementalProblems() {
		return OneOrMore(IncrementalProblem(), ZeroOrMore(IncrementalProblems()));
	}


	public Rule StepperStart() {
		return Sequence(
				Space(),
				//FirstOf(With(), StepperProblem(), StepperServe())
				With()
		);
	}

	boolean enterProblemScope(String id) {
		if(!problems.containsKey(id)) {
			if(type.equals(KodkodServer.Feature.PLAIN_STEPPER))
				problems.put(id, KodkodProblem.stepper(id));
			else if(type.equals(KodkodServer.Feature.TEMPORAL))
				problems.put(id, KodkodProblem.temporal(id));
			else if(type.equals(KodkodServer.Feature.TARGET_ORIENTED))
				problems.put(id, KodkodProblem.targetOriented(id));
			else
				throw new UnsupportedOperationException(type.toString());
		}
		this.info("entering scope: <"+id+">; type="+type+"; problem hash="+problems.get(id).hashCode());
		this.currentID = id;
		setProblem(problems.get(id));
		return true;
	}

	boolean checkCurrentProblemIsInitialized() {
		if(problem() == null || problem().asserts() == null || problem().bounds() == null) {
			this.info("problem not initialized: <"+this.currentID+">");
			throw new IllegalStateException("problem (id="+currentID+") not initialized");
		}
		return true;
	}

	public Rule With() {
		return Sequence(
				Space(),
				LPAR,
				WITH,
				StringLiteral(),
				// StringLiteral() contains the trailing blank space
				//Space(),
				enterProblemScope(popString()),
				FirstOf(StepperProblem(), StepperServe()),
				enterProblemScope(""),
				RPAR,
				EOI
		);
	}


	// FirstOf tries all args in order, succeeds on the first success
	// Sequence tries all args in order, succeeds only if all args succeed

	/**
	 * A stepper problem command. Uses current problem.
	 * @throws IllegalStateException If current problem hasn't been initialized
	 */
	public Rule StepperServe() {
		return Sequence(
				checkCurrentProblemIsInitialized(),
				Space(),
				FirstOf(Solve(),
						Clear(),
						Exit(),
						// an evaluator invocation vs. last instance
						Sequence(ZeroOrMore(DefNode()), Evaluate()))
				);
	}

	/**
	 *  A stepper problem definition. Does _not_ include (solve), etc. Uses current problem.
 	 */
	@Cached
	public Rule StepperProblem() {
		return Sequence(Space(),
				        currentProblem.startBuild(),
				        Configure(),
				        DeclareUniverse(),
				        Optional(DeclareInts()),
				        ZeroOrMore(
								FirstOf(
										DeclareRelation(),
										DeclareVarRelation(),
										DefNode(),
										Assert())),
				        currentProblem.endBuild());
	}

	@Cached
	public Rule TargetOrientedProblem() {
		return Sequence(Space(), currentProblem.startBuild(), Configure(), DeclareUniverse(), Optional(DeclareInts()),
				ZeroOrMore(FirstOf(DeclareRelation(), DeclareVarRelation(), DefNode(), Assert(), Target(),
						TargetOption())),
				currentProblem.endBuild(), StepperServe());
	}

	public Rule Target() {
		final Var<List<Relation>> rels = new Var<>();
		final Var<TupleSet> tuple = new Var<>();
		return Sequence(LPAR, String("target"), Space(), Use('r'), rels.set(new ArrayList<Relation>(4)),
				rels.get().add(popRelation()), ZeroOrMore(Use('r'), rels.get().add(popRelation())), LBRK, TupleSet(),
				tuple.set(popTupleSet()), RBRK, RPAR, currentProblem.setTarget(rels.get(), tuple.get()));
	}

	public Rule TargetOption() {
		return Sequence(LPAR, String("target-option"), Space(), TargetMode(), RPAR);
	}

	public Rule TargetMode() {
		final Var<String> target_mode = new Var<>();
		return Sequence(String("target-mode"), Space(),
				FirstOf(Sequence(CLOSE_RETARGET, target_mode.set("close_retarget")),
						Sequence(FAR_RETARGET, target_mode.set("far_retarget")),
						Sequence(CLOSE_NORETARGET, target_mode.set("close")),
						Sequence(FAR_NORETARGET, target_mode.set("far")),
						Sequence(COVER, target_mode.set("cover"))
				),
				currentProblem.setTargetType(target_mode.get()));
	}

	/**
	 * @return Exit? Configure Universe DefineInts? IncrementalProblem
	 */
	@Cached
	public Rule Problem() {
		return Sequence(Space(), Optional(Exit()), currentProblem.startBuild(), Configure(), DeclareUniverse(),
				Optional(DeclareInts()),
				ZeroOrMore(FirstOf(DeclareRelation(), DeclareVarRelation(), DefNode(), Assert())), currentProblem.endBuild(),
				Serve());
	}

	/**
	 * @return DefineRelation* DefineNode* Assert* Serve
	 */
	@Cached
	public Rule IncrementalProblem() {
		return Sequence(Space(), currentProblem.startBuild(),
				ZeroOrMore(FirstOf(DeclareRelation(), DeclareVarRelation(), DefNode(), Assert())), currentProblem.endBuild(),
				Serve());
	}

	// -------------------------------------------------------------------------
	// Configuration options
	// -------------------------------------------------------------------------

	/**
	 * @return (LPAR CONFIG ( ( : solver Solver) | (:bitwidth NatLiteral) |
	 *         (:produce-cores BooleanLiteral) | (:verbosity NatLiteral) |
	 *         (:max-solutions NatLiteral))+ RPAR)*
	 **/
	Rule Configure() {
		return ZeroOrMore(LPAR, CONFIG,
				OneOrMore(":",
						FirstOf(Sequence(Keyword("solver"), SatSolver(), currentProblem.setSolver(out, (SATFactory) pop())),
								Sequence(Keyword("bitwidth"), NatLiteral(), currentProblem.setBitwidth(popInt())),
								// Sequence(Keyword("produce-cores"), BoolLiteral(),
								// problem.setCoreExtraction(popBool())),
								Sequence(Keyword("log-trans"), NatLiteral(), currentProblem.setLogTranslation(popInt())),
								Sequence(Keyword("core-gran"), NatLiteral(), currentProblem.setCoreGranularity(popInt())),
								Sequence(Keyword("core-minimization"), StringLiteral(), currentProblem.setCoreMinimization(popString())),
								Sequence(Keyword("verbosity"), NatLiteral(), currentProblem.setVerbosity(level(popInt()))),
								Sequence(Keyword("sb"), NatLiteral(), currentProblem.setSB(popInt())),
								Sequence(Keyword("max-trace-length"), NatLiteral(), currentProblem.setMaxTraceLength(popInt())),
								Sequence(Keyword("min-trace-length"), NatLiteral(), currentProblem.setMinTraceLength(popInt())),
								Sequence(Keyword("skolem-depth"), IntLiteral(), currentProblem.setSkolemDepth(popInt())),
								Sequence(Keyword("max-solutions"), NatLiteral(), currentProblem.setMaxSolutions(popInt())))),
				RPAR);
	}

	/**
	 * @return MiniSatProver | MiniSat | Glucose | Lingeling | SAT4J
	 */
	@SuppressSubnodes
	@MemoMismatches
	Rule SatSolver() {
		return FirstOf(Sequence(Keyword("MiniSatProver"), push(SATFactory.MiniSatProver)),
				Sequence(Keyword("MiniSat"), push(SATFactory.MiniSat)),
				Sequence(Keyword("Glucose"), push(SATFactory.Glucose)),
				Sequence(Keyword("Lingeling"), push(SATFactory.Lingeling)),
				Sequence(Keyword("SAT4J"), push(SATFactory.DefaultSAT4J)),
				Sequence(Keyword("TargetSATSolver"), push(SATFactory.PMaxSAT4J)),
				Sequence(Keyword("PMaxSAT4J"), push(SATFactory.PMaxSAT4J)),
				Sequence(Sequence(FilePathLiteral(), Space()),
						push(SATFactory.externalFactory(popString(), "customSolver.temp", false, false)))); // Removed
																											// for
																											// Pardinus
	}

	// -------------------------------------------------------------------------
	// Universe, int builder and relation declarations/builder
	// -------------------------------------------------------------------------

	/**
	 * @return LPAR UNIV NatLiteral RPAR
	 */
	Rule DeclareUniverse() {
		return Sequence(LPAR, UNIV, NatLiteral(), currentProblem.declareUniverse(popInt()), RPAR);
	}

	/**
	 * @return LPAR INTS LBRK (LPAR IntLiteral NatLiteral RPAR)+ RBRK RPAR
	 */
	Rule DeclareInts() {
		final Var<List<Integer>> ints = new Var<>();
		return Sequence(LPAR, INTS, LBRK, ints.set(new ArrayList<Integer>(16)),
				OneOrMore(LPAR, IntLiteral(), ints.get().add(popInt()), NatLiteral(), ints.get().add(popInt()), RPAR),
				RBRK, RPAR, currentProblem.declareInts(ints.get()));
	}

	/**
	 * @return LPAR Identifier('r')+ LBRK TupleSet [DOUBLECOLON? TupleSet]? RBRK
	 *         RPAR
	 */
	Rule DeclareRelation() {
		final Var<List<String>> names = new Var<>();
		final Var<TupleSet> lower = new Var<>(), upper = new Var<>();
		return Sequence(LPAR, Identifier('r'), names.set(new ArrayList<String>(4)), names.get().add(popString()),
				ZeroOrMore(Identifier('r'), names.get().add(popString())), LBRK, TupleSet(), lower.set(popTupleSet()),
				FirstOf(Sequence(DOUBLECOLON, upper.set(lower.get()), TupleSet(),
						upper.set(upper.isSet() ? union(upper.get(), popTupleSet()) : popTupleSet())),
						Sequence(EMPTY, upper.set(lower.get()))),
				RBRK, RPAR, currentProblem.declareRelations(names.get(), lower.get(), upper.get()));
	}

	/**
	 * @return LPAR Identifier('x')+ LBRK TupleSet [DOUBLECOLON? TupleSet]? RBRK
	 *         RPAR Added for Electrum
	 */
	Rule DeclareVarRelation() {
		final Var<List<String>> names = new Var<>();
		final Var<TupleSet> lower = new Var<>(), upper = new Var<>();
		return Sequence(LPAR, Identifier('x'), names.set(new ArrayList<String>(4)), names.get().add(popString()),
				ZeroOrMore(Identifier('x'), names.get().add(popString())), LBRK, TupleSet(), lower.set(popTupleSet()),
				FirstOf(Sequence(DOUBLECOLON, upper.set(lower.get()), TupleSet(),
						upper.set(upper.isSet() ? union(upper.get(), popTupleSet()) : popTupleSet())),
						Sequence(EMPTY, upper.set(lower.get()))),
				RBRK, RPAR, currentProblem.declareVarRelations(names.get(), lower.get(), upper.get()));
	}

	// -------------------------------------------------------------------------
	// TupleSets and Tuples
	// -------------------------------------------------------------------------

	/**
	 * @return RelationReference | VarRelationReference | ExprLiteral | TupleSetEnum
	 *         | TupleSetExpr
	 */

	Rule TupleSet() {
		return FirstOf(Sequence(Use('r'), push(valueOf(popRelation(), currentProblem.allBounds()))),
				Sequence(Use('x'), push(valueOf(popRelation(), currentProblem.allBounds()))),
				Sequence(ExprLiteral(), push(valueOf(popExpr(), currentProblem.allBounds()))), TupleSetEnum(), TupleSetExpr());
	}

	/**
	 * @return LPAR (PLUS|PRODUCT|INTERSECT|MINUS) TupleSet+ RPAR
	 */
	Rule TupleSetExpr() {
		return Sequence(LPAR,
				FirstOf(TupleSetExpr(ARROW, ExprOperator.PRODUCT), TupleSetExpr(PLUS, ExprOperator.UNION),
						TupleSetExpr(AMP, ExprOperator.INTERSECTION), TupleSetExpr(MINUS, ExprOperator.DIFFERENCE)),
				RPAR);
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY
	Rule TupleSetExpr(Rule opRule, ExprOperator op) {
		final Var<TupleSet> first = new Var<>();
		final Var<List<TupleSet>> rest = new Var<>();

		return FirstOf(Sequence(ACTION(first.enterFrame()), ACTION(rest.enterFrame()),

				opRule, rest.set(new ArrayList<TupleSet>(4)), TupleSet(), first.set(popTupleSet()),
				ZeroOrMore(TupleSet(), rest.get().add(popTupleSet())), push(compose(op, first.get(), rest.get())),

				ACTION(first.exitFrame()), ACTION(rest.exitFrame())),

				Sequence(ACTION(first.exitFrame()), ACTION(rest.exitFrame()), NOTHING));
	}

	/**
	 * @return LWING (Tuple ((ELLIPSIS Tuple) | (HASH Tuple) | Tuple*))? RWING
	 */
	Rule TupleSetEnum() {
		final Var<TupleSet> ts = new Var<>();
		return Sequence(
				LWING, FirstOf(
						Sequence(Tuple(),
								FirstOf(Sequence(ELLIPSIS, Tuple(), swap(), ts.set(range(popTuple(), popTuple()))),
										Sequence(HASH, Tuple(), swap(), ts.set(area(popTuple(), popTuple()))),
										Sequence(ts.set(setOf(popTuple())),
												ZeroOrMore(Tuple(), add(ts.get(), popTuple()))))),
						Sequence(EMPTY, ts.set(valueOf(Expression.NONE, currentProblem.allBounds())))),
				RWING, push(ts.get()));
	}

	/**
	 * @return LPAR NatLiteral+ RPAR
	 */
	@SuppressSubnodes
	Rule Tuple() {
		final Var<List<Integer>> t = new Var<List<Integer>>();
		return Sequence(LPAR, t.set(new ArrayList<Integer>(4)), OneOrMore(NatLiteral(), t.get().add(popInt())), RPAR,
				push(tuple(currentProblem.allBounds().universe().factory(), t.get())));
	}

	// -------------------------------------------------------------------------
	// Register defs and uses
	// -------------------------------------------------------------------------

	/**
	 * @return LPAR NodeDef RPAR
	 */
	Rule DefNode() {
		return Sequence(LPAR, NodeDef(), RPAR);
	}

	/**
	 * @return Def(' e ', Expr) | Def('i', IntExpr) | Def('f', Constraint)
	 */
	Rule NodeDef() {
		return FirstOf(Def('e', Expr()), Def('i', IntExpr()), Def('f', Constraint()));
	}

	@SuppressSubnodes
	@Cached
	/** @return Identifier(varPrefix) varValue */
	Rule Def(char varPrefix, Rule varValue) {
		final Var<String> varName = new Var<>();
		return Sequence(Identifier(varPrefix), varName.set(popString()), varValue,
				env().def(varPrefix, varName.get(), (Node) pop()));
	}

	@SuppressSubnodes
	@Cached
	/** @return Identifier(varPrefix) */
	Rule Use(char varPrefix) {
		return Sequence(
				Identifier(varPrefix),
				currentProblem.boundForcedAtomIfNeeded(varPrefix, peekString()),
				push(lookup(env(), varPrefix, popString())));
	}

	Object lookup(StringDefEnv env, char varPrefix, String val) {
		try {
			return env.use(varPrefix, val);
		} catch(ActionException ae) {
			this.info("error: environment didn't contain: "+val);
			throw ae;
		}
	}


	// -------------------------------------------------------------------------
	// Assertions and commands
	// -------------------------------------------------------------------------

	/**
	 * @return LPAR ASSERT Use('f')+ RPAR
	 */
	Rule Assert() {
		return Sequence(LPAR, ASSERT, OneOrMore(Use('f'), currentProblem.assertFormula(popFormula())), RPAR);
	}

	/**
	 * @return LPAR EVALUATE Use('e') | Use('i') | Use('f') RPAR
	 */
	Rule Evaluate() {
		return Sequence(LPAR, EVALUATE, FirstOf(
				Sequence(Use('e'), currentProblem.evaluate(popExpr())),
				Sequence(Use('i'), currentProblem.evaluate(popIntExpr())),
				Sequence(Use('f'), currentProblem.evaluate(popFormula()))),
				RPAR);
	}

	/**
	 * @return (Solve Clear ?) | Clear | Exit?
	 */
	Rule Serve() {
		return Sequence(FirstOf(Sequence(Solve(), Optional(Clear())), Clear()), Optional(Exit()), Optional(EOI));
	}

	/**
	 * @return LPAR SOLVE RPAR
	 * @ensures setProblem(this.problem.solve ())
	 **/
	Rule Solve() {
		//return Sequence(LPAR, SOLVE, RPAR, setProblem(problem.solve(out)));
		return Sequence(LPAR, SOLVE, Optional(StringLiteral()), RPAR,
				setProblem(currentProblem.solve(out, getContext().getValueStack().isEmpty() ? "" : popString())));
	}

	/**
	 * @return LPAR CLEAR RPAR
	 * @ensures setProblem(this.problem.clear ())
	 **/
	Rule Clear() {
		return Sequence(LPAR, CLEAR, RPAR, setProblem(currentProblem.clear(out)));
	}

	/**
	 * @return LPAR EXIT RPAR
	 * @ensures setProblem(null)
	 **/
	Rule Exit() {
		return Sequence(LPAR, EXIT, RPAR, setProblem(null));
	}

	// -------------------------------------------------------------------------
	// Formulas
	// -------------------------------------------------------------------------

	/**
	 * @return Use(' f ') | BoolLiteral | LPAR ... RPAR note: always, after,
	 *         eventually added for Electrum
	 **/
	Rule Constraint() {
		return FirstOf(Use('f'), ConstraintLiteral(), Sequence(LPAR,
				FirstOf(ExprComparison(IN, ExprCompOperator.SUBSET), EqComparison(),
						IntExprComparison(LTE, IntCompOperator.LTE), IntExprComparison(LT, IntCompOperator.LT),
						IntExprComparison(GTE, IntCompOperator.GTE), IntExprComparison(GT, IntCompOperator.GT),
						MultConstraint(ONE, Multiplicity.ONE), MultConstraint(LONE, Multiplicity.LONE),
						MultConstraint(NO, Multiplicity.NO), SomeConstraint(), QuantConstraint(ALL, Quantifier.ALL),
						NotConstraint(),

						AlwaysConstraint(), // Electrum Constraint
						EventuallyConstraint(), // Electrum Constraint
						AfterConstraint(), // Electrum Constraints
						HistoricallyConstraint(), // Electrum Constraint
						OnceConstraint(), // Electrum Constraint
						BeforeConstraint(), // Electrum Constraints
						TempConstraint(UNTIL, TemporalOperator.UNTIL), // Electrum Constraints
						TempConstraint(RELEASES, TemporalOperator.RELEASES), // Electrum Constraints
						TempConstraint(TRIGGERED, TemporalOperator.TRIGGERED), // Electrum Constraints
						TempConstraint(SINCE, TemporalOperator.SINCE), // Electrum Constraints

						NaryConstraint(AND, FormulaOperator.AND), NaryConstraint(OR, FormulaOperator.OR),
						NaryConstraint(IMPLIES, FormulaOperator.IMPLIES), NaryConstraint(IFF, FormulaOperator.IFF),
						Acyclic(), TotalOrder(), Let(Constraint())),
				RPAR));
	}

	/**
	 * @return BoolLiteral
	 */
	Rule ConstraintLiteral() {
		return Sequence(BoolLiteral(), push(Formula.constant(popBool())));
	}

	/**
	 * @return EQ ((Expr Expr)|(IntExpr IntExpr))
	 */
	Rule EqComparison() {
		return Sequence(EQ,
				FirstOf(ExprComparison(EMPTY, ExprCompOperator.EQUALS), IntExprComparison(EMPTY, IntCompOperator.EQ)));
	}

	@Cached
	/** @return cmpRule Expr Expr */
	Rule ExprComparison(Rule cmpRule, ExprCompOperator cmp) {
		return Sequence(cmpRule, Expr(), Expr(), swap(), push(compare(cmp, popExpr(), popExpr())));
	}

	@Cached
	/** @return cmpRule IntExpr IntExpr */
	Rule IntExprComparison(Rule cmpRule, IntCompOperator cmp) {
		return Sequence(cmpRule, IntExpr(), IntExpr(), swap(), push(popIntExpr().compare(cmp, popIntExpr())));
	}

	@Cached
	/** @return multRule Expr */
	Rule MultConstraint(Rule multRule, Multiplicity mult) {
		return Sequence(multRule, Expr(), push(popExpr().apply(mult)));
	}

	@Cached
	/** @return SOME (Expr | QuantifiedConstraint) */
	Rule SomeConstraint() {
		return Sequence(SOME,
				FirstOf(MultConstraint(EMPTY, Multiplicity.SOME), QuantConstraint(EMPTY, Quantifier.SOME)));
	}

	@Cached
	/** @return quantRule VarDecls Constraint */
	Rule QuantConstraint(Rule quantRule, Quantifier quant) {
		return Sequence(quantRule, VarDecls(), Constraint(), push(popFormula().quantify(quant, popDecls())), swap(),
				drop());
	}

	/**
	 * @return NOT Constraint
	 */
	Rule NotConstraint() {
		return Sequence(NOT, Constraint(), push(popFormula().not()));
	}

	// Electrum unary constraints /////////////////////////////////
	Rule AlwaysConstraint() {
		return Sequence(ALWAYS, Constraint(), push(popFormula().always()));
	}
	Rule EventuallyConstraint() {
		return Sequence(EVENTUALLY, Constraint(), push(popFormula().eventually()));
	}
	Rule AfterConstraint() {
		return Sequence(AFTER, Constraint(), push(popFormula().after()));
	}
	Rule HistoricallyConstraint() { return Sequence(HISTORICALLY, Constraint(), push(popFormula().historically())); }
	Rule OnceConstraint() {
		return Sequence(ONCE, Constraint(), push(popFormula().once()));
	}
	Rule BeforeConstraint() {
		return Sequence(BEFORE, Constraint(), push(popFormula().before()));
	}

	
	@Cached
	/** @return Temporal Rule Constraint+ */
	Rule TempConstraint(Rule rule, TemporalOperator op) {
		final Var<List<Formula>> args = new Var<>();

		return FirstOf(
				Sequence(ACTION(args.enterFrame()), rule, args.set(new ArrayList<Formula>(4)),
						OneOrMore(Constraint(), args.get().add(popFormula())), push(compose_temp(op, args.get())),
						ACTION(args.exitFrame())),

				Sequence(ACTION(args.exitFrame()), NOTHING));
	}

	//////////////////////////////////////////////////////
	

	// WARNING CHANGED HACK USES VAR RECURSIVELY
	@Cached
	/** @return opRule Constraint+ */
	Rule NaryConstraint(Rule opRule, FormulaOperator op) {
		final Var<List<Formula>> args = new Var<>();

		return FirstOf(
				Sequence(ACTION(args.enterFrame()), opRule, args.set(new ArrayList<Formula>(4)),
						OneOrMore(Constraint(), args.get().add(popFormula())), push(compose(op, args.get())),
						ACTION(args.exitFrame())),

				Sequence(ACTION(args.exitFrame()), NOTHING));
	}


	/**
	 * @return ACYCLIC Use('r')
	 */
	Rule Acyclic() {
		return Sequence(ACYCLIC, Use('r'), push(acyclic(popRelation())));
	}

	/**
	 * @return TOTAL_ORD Use('r') Use('r') Use('r') Use('r')
	 */
	Rule TotalOrder() {
		return Sequence(TOTAL_ORD, Use('r'), Use('r'), Use('r'), Use('r'), swap4(),
				push(totalOrder(popRelation(), popRelation(), popRelation(), popRelation())));
	}

	// -------------------------------------------------------------------------
	// Quantified variable declarations
	// -------------------------------------------------------------------------

	public <V> Boolean pushToStack(Var<DefaultValueStack> stack, V val) {
		// if (val )
		stack.get().push(val);
		// pnt(stack);
		// pnt(stack.get());
		// stack.get().push(3);
		return true;
	}

	public <V> Boolean initializeVar(Var<V> var, V val) {
		if (var.get() == null) {
			var.set(val);
		}
		return true;
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY

	/**
	 * @return LPAR VarDecl+ RPAR
	 */
	Rule VarDecls() {
		final Var<Decls> decls = new Var<>();
		return FirstOf(
				Sequence(ACTION(decls.enterFrame()), LPAR, push(env().extend()), VarDecl(), decls.set(popDecls()),
						ZeroOrMore(Sequence(VarDecl(), decls.set(decls.get().and(popDecls())))), RPAR,
						push(decls.get()), ACTION(decls.exitFrame())),

				Sequence(ACTION(decls.exitFrame()), NOTHING));
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY

	/**
	 * @return LBRK Identifier('v') :[LONE|ONE|SOME|SET] Expr RBRK
	 */
	Rule VarDecl() {
		final Var<String> varName = new Var<>();
		final Var<Decl> decl = new Var<>();

		return FirstOf(
				Sequence(ACTION(varName.enterFrame()), ACTION(decl.enterFrame()), LBRK, Identifier('v'),
						varName.set(popString()), Ch(':'), Space(),
						FirstOf(VarMult(ONE, Multiplicity.ONE), VarMult(LONE, Multiplicity.LONE),
								VarMult(SOME, Multiplicity.SOME), VarMult(SET, Multiplicity.SET),
								VarMult(Space(), Multiplicity.ONE)),
						Expr(), swap(), RBRK, decl.set(declareVariable(varName.get(), popMult(), popExpr())),
						peekEnv().def('v', varName.get(), decl.get().variable()), push(decl.get()),

						ACTION(varName.exitFrame()), ACTION(decl.exitFrame())),

				Sequence(ACTION(varName.exitFrame()), ACTION(decl.exitFrame()), NOTHING));
	}

	@Cached
	/** @return multRule */
	Rule VarMult(Rule multRule, Multiplicity mult) {
		return Sequence(multRule, push(mult));
	}

	// -------------------------------------------------------------------------
	// Relational expressions
	// -------------------------------------------------------------------------

	/**
	 * @return Use(' e ') | Use('r') | Use('v') | ExprLiteral | LPAR ... RPAR |
	 *         SetComprehension
	 */
	// var x
	Rule Expr() {
		return FirstOf(Use('e'), Use('r'), Use('v'), Use('a'), Use('x'), ExprLiteral(),
				Sequence(LPAR, FirstOf(NaryExpr(DOT, ExprOperator.JOIN), NaryExpr(PLUSPLUS, ExprOperator.OVERRIDE),
						NaryExpr(PLUS, ExprOperator.UNION), NaryExpr(AMP, ExprOperator.INTERSECTION),
						NaryExpr(ARROW, ExprOperator.PRODUCT), NaryExpr(MINUS, ExprOperator.DIFFERENCE),
						UnaryExpr(TILDE, ExprOperator.TRANSPOSE), UnaryExpr(HAT, ExprOperator.CLOSURE),
						UnaryExpr(PRIME, TemporalOperator.PRIME),
						UnaryExpr(STAR, ExprOperator.REFLEXIVE_CLOSURE), IntToExprCast(SET, IntCastOperator.BITSETCAST),
						IntToExprCast(LONE, IntCastOperator.INTCAST), IfExpr(), Let(Expr()), Projection()), RPAR),
				SetComprehension());
	}

	/**
	 * @return ITE Constraint Expr Expr
	 */
	Rule IfExpr() {
		return Sequence(ITE, Constraint(), Expr(), Expr(), swap3(), push(ite(popFormula(), popExpr(), popExpr())));
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY
	// @Cached /** @return opRule Expr+ */
	Rule NaryExpr(Rule opRule, ExprOperator op) {
		final Var<List<Expression>> args = new Var<>();

		return FirstOf(Sequence(ACTION(args.enterFrame()), opRule, args.set(new ArrayList<Expression>(4)),
				OneOrMore(Expr(), args.get().add(popExpr())), push(compose(op, args.get())), ACTION(args.exitFrame())),

				Sequence(ACTION(args.exitFrame()), NOTHING));
	}

	@Cached
	/** @return opRule Expr */
	Rule UnaryExpr(Rule opRule, ExprOperator op) {

		return Sequence(opRule, Expr(), push(compose(op, Collections.singletonList(popExpr()))));
	}
	Rule UnaryExpr(Rule opRule, TemporalOperator op) {
		return Sequence(opRule, Expr(), push(compose(op, Collections.singletonList(popExpr()))));
	}

	@Cached
	/** @return castRule IntExpr */
	Rule IntToExprCast(Rule castRule, IntCastOperator castOp) {
		return Sequence(castRule, IntExpr(), push(popIntExpr().cast(castOp)));
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY

	/**
	 * @return AT Expr() IntExpr()+
	 */
	Rule Projection() {
		final Var<Expression> expr = new Var<>();
		final Var<List<IntExpression>> cols = new Var<>();
		return FirstOf(Sequence(ACTION(expr.enterFrame()), ACTION(cols.enterFrame()),

				AT, Expr(), expr.set(popExpr()), cols.set(new ArrayList<IntExpression>(4)),
				OneOrMore(IntExpr(), cols.get().add(popIntExpr())),
				push(expr.get().project(cols.get().toArray(new IntExpression[cols.get().size()]))),
				ACTION(expr.exitFrame()), ACTION(cols.exitFrame())),

				Sequence(ACTION(expr.exitFrame()), ACTION(cols.exitFrame()), NOTHING));
	}

	/**
	 * @return LWING VarDecls Constraint RWING
	 */
	Rule SetComprehension() {
		return Sequence(LWING, VarDecls(), Constraint(), swap3(), drop(), RWING,
				push(comprehension(popDecls(), popFormula())));
	}

	// -------------------------------------------------------------------------
	// Bitvector expressions
	// -------------------------------------------------------------------------

	/**
	 * @return Use(' i ') | IntLiteral | LPAR ... RPAR
	 */
	Rule IntExpr() {
		return FirstOf(Use('i'), IntExprLiteral(),
				Sequence(LPAR,
						FirstOf(ExprToIntCast(HASH, ExprCastOperator.CARDINALITY), SumIntExpr(), MinusIntExpr(),
								NaryIntExpr(PLUS, IntOperator.PLUS), NaryIntExpr(STAR, IntOperator.MULTIPLY),
								NaryIntExpr(DIV, IntOperator.DIVIDE), NaryIntExpr(MOD, IntOperator.MODULO),
								NaryIntExpr(AMP, IntOperator.AND), NaryIntExpr(BAR, IntOperator.OR),
								NaryIntExpr(HAT, IntOperator.XOR), NaryIntExpr(SHL, IntOperator.SHL),
								NaryIntExpr(SHR, IntOperator.SHR), NaryIntExpr(SHA, IntOperator.SHA),
								UnaryIntExpr(TILDE, IntOperator.NOT), UnaryIntExpr(ABS, IntOperator.ABS),
								UnaryIntExpr(SGN, IntOperator.SGN), IfIntExpr(), Let(IntExpr())),
						RPAR));
	}

	/**
	 * @return IntLiteral
	 */
	Rule IntExprLiteral() {
		return Sequence(IntLiteral(), push(IntConstant.constant(popInt())));
	}

	/**
	 * @return ITE Constraint IntExpr IntExpr
	 */
	Rule IfIntExpr() {
		return Sequence(ITE, Constraint(), IntExpr(), IntExpr(), swap3(),
				push(popFormula().thenElse(popIntExpr(), popIntExpr())));
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY
	@Cached
	/** @return opRule IntExpr+ */
	Rule NaryIntExpr(Rule opRule, IntOperator op) {
		final Var<List<IntExpression>> args = new Var<>();

		return FirstOf(Sequence(ACTION(args.enterFrame()),

				opRule, args.set(new ArrayList<IntExpression>(4)), OneOrMore(IntExpr(), args.get().add(popIntExpr())),
				push(compose(op, args.get())),

				ACTION(args.exitFrame())),

				Sequence(ACTION(args.exitFrame()), NOTHING));
	}

	// WARNING CHANGED HACK USES VAR RECURSIVELY

	/**
	 * @return - IntExpr+
	 */
	Rule MinusIntExpr() {
		final Var<List<IntExpression>> args = new Var<>();
		return FirstOf(Sequence(ACTION(args.enterFrame()), MINUS, args.set(new ArrayList<IntExpression>(4)),
				OneOrMore(IntExpr(), args.get().add(popIntExpr())),
				push(compose(args.get().size() == 1 ? IntOperator.NEG : IntOperator.MINUS, args.get())),
				ACTION(args.exitFrame())), Sequence(ACTION(args.exitFrame()), NOTHING));
	}

	@Cached
	/** @return opRule IntExpr */
	Rule UnaryIntExpr(Rule opRule, IntOperator op) {
		return Sequence(opRule, IntExpr(), push(compose(op, Collections.singletonList(popIntExpr()))));
	}

	@Cached
	/** @return castOp Expr */
	Rule ExprToIntCast(Rule castRule, ExprCastOperator castOp) {
		return Sequence(castRule, Expr(), push(cast(castOp, popExpr())));
	}

	/**
	 * @return SUM (Expr | (VarDecls IntExpr))
	 */
	Rule SumIntExpr() {
		return Sequence(SUM, FirstOf(ExprToIntCast(EMPTY, ExprCastOperator.SUM),
				Sequence(VarDecls(), IntExpr(), swap3(), drop(), push(sum(popDecls(), popIntExpr())))));
	}

	// -------------------------------------------------------------------------
	// Let
	// -------------------------------------------------------------------------
	@Cached
	/** @return LET LPAR (LRBRK NodeDef RBRK)+ RPAR bodyRule */
	Rule Let(Rule bodyRule) {
		return Sequence(LET, push(env().extend()), LPAR, OneOrMore(Sequence(LBRK, NodeDef(), RBRK)), RPAR, bodyRule,
				swap(), drop());
	}

	// -------------------------------------------------------------------------
	// Literals
	// -------------------------------------------------------------------------

	/**
	 * @return MINUS?NatLiteral
	 */
	@SuppressSubnodes
	Rule IntLiteral() {
		return Sequence(Sequence(Optional(Ch('-')), OneOrMore(Digit())), push(Integer.parseInt(match())), Space());
	}

	/**
	 * @return Digit+
	 */
	@SuppressSubnodes
	Rule NatLiteral() {
		return Sequence(OneOrMore(Digit()), push(Integer.parseInt(match())), Space());
	}

	@SuppressSubnodes
	Rule StringLiteral() {
		return Sequence(OneOrMore(NotSpace()), push(match()), Space());
	}

	/**
	 * @return TRUE | FALSE
	 */
	@SuppressSubnodes
	Rule BoolLiteral() {
		return FirstOf(Sequence(TRUE, push(Boolean.TRUE)), Sequence(FALSE, push(Boolean.FALSE)));
	}

	/**
	 * @return UNIV | NONE | IDEN | INTS
	 */
	@SuppressSubnodes
	Rule ExprLiteral() {
		return FirstOf(ExprLiteral(UNIV, Expression.UNIV), ExprLiteral(NONE, Expression.NONE),
				ExprLiteral(IDEN, Expression.IDEN), ExprLiteral(INTS, Expression.INTS));
	}

	@SuppressSubnodes
	Rule FilePathLiteral() {
		return Sequence('"', ZeroOrMore(FilePathChar()).suppressSubnodes(), push(match()), '"');
	}

	@Cached
	/** @return litRule */
	Rule ExprLiteral(Rule litRule, Expression lit) {
		return Sequence(litRule, push(lit));
	}

	// -------------------------------------------------------------------------
	// Identifiers
	// -------------------------------------------------------------------------

	/**
	 * @return Ch(prefix)[0-9]+
	 */
	@SuppressSubnodes
	Rule Identifier(char prefix) {
		return Sequence(Ch(prefix), Ch(':'), StringLiteral(), Space());
	}

	// -------------------------------------------------------------------------
	// Spacing
	// -------------------------------------------------------------------------
	Rule Space() {
		return ZeroOrMore(FirstOf(OneOrMore(AnyOf(" \t\r\n\f")), // whitespace
				Sequence(";", // end of line comment
						ZeroOrMore(TestNot(AnyOf("\r\n")), ANY), FirstOf("\r\n", '\r', '\n', EOI))));
	}

	// -------------------------------------------------------------------------
	// Separators
	// -------------------------------------------------------------------------
	final Rule LBRK = Terminal("["), RBRK = Terminal("]");
	final Rule LWING = Terminal("{"), RWING = Terminal("}");
	final Rule LPAR = Terminal("("), RPAR = Terminal(")");

	// -------------------------------------------------------------------------
	// Keywords and symbols
	// -------------------------------------------------------------------------
	final Rule CONFIG = Keyword("configure");
	final Rule ASSERT = Keyword("assert");
	final Rule EVALUATE = Keyword("evaluate");
	final Rule SOLVE = Keyword("solve");
	final Rule CLEAR = Keyword("clear");
	final Rule WITH = Keyword("with");
	final Rule EXIT = Keyword("exit");

	final Rule UNIV = Keyword("univ");
	final Rule NONE = Keyword("none");
	final Rule IDEN = Keyword("iden");
	final Rule INTS = Keyword("ints");
	final Rule TRUE = Keyword("true");
	final Rule FALSE = Keyword("false");

	final Rule LET = Keyword("let");
	final Rule ALL = Keyword("all");
	final Rule SOME = Keyword("some");
	final Rule LONE = Keyword("lone");
	final Rule ONE = Keyword("one");
	final Rule NO = Keyword("no");
	final Rule SET = Keyword("set");

	// Electrum key words
	final Rule ALWAYS = Keyword("always");
	final Rule AFTER = Keyword("after");
	final Rule EVENTUALLY = Keyword("eventually");
	final Rule ONCE = Keyword("once");
	final Rule HISTORICALLY = Keyword("historically");
	final Rule BEFORE = Keyword("before");
	final Rule UNTIL = Keyword("until");
	final Rule RELEASES = Keyword("releases");
	final Rule SINCE = Keyword("since");
	final Rule TRIGGERED = Keyword("triggered");


	final Rule IN = Keyword("in");
	final Rule ITE = Keyword("ite");
	final Rule SUM = Keyword("sum");
	final Rule ABS = Keyword("abs");
	final Rule SGN = Keyword("sgn");

	final Rule ACYCLIC = Keyword("acyclic");
	final Rule TOTAL_ORD = Keyword("total-order");

	final Rule AT = Terminal("@");
	final Rule AND = Terminal("&&");
	final Rule OR = Terminal("||");
	final Rule NOT = Terminal("!");
	final Rule IFF = Terminal("<=>");
	final Rule IMPLIES = Terminal("=>");

	final Rule ELLIPSIS = Terminal("...");
	final Rule COLON = Terminal(":", Ch(':'));
	final Rule DOUBLECOLON = Terminal("::");
	final Rule HASH = Terminal("#");

	final Rule EQ = Terminal("=", Ch('>'));
	final Rule GTE = Terminal(">=");
	final Rule GT = Terminal(">", AnyOf("=>"));
	final Rule LTE = Terminal("<=");
	final Rule LT = Terminal("<", AnyOf("=<"));
	final Rule PLUS = Terminal("+", Ch('+'));
	final Rule MINUS = Terminal("-", Ch('>'));
	final Rule AMP = Terminal("&");
	final Rule PLUSPLUS = Terminal("++");
	final Rule ARROW = Terminal("->");
	final Rule DOT = Terminal(".");
	final Rule TILDE = Terminal("~");
	final Rule HAT = Terminal("^");
	final Rule STAR = Terminal("*");
	final Rule PRIME = Terminal("prime");
	final Rule DIV = Terminal("/");
	final Rule MOD = Terminal("%");
	final Rule BAR = Terminal("|");
	final Rule SHL = Terminal("<<");
	final Rule SHR = Terminal(">>>");
	final Rule SHA = Terminal(">>", Ch('>'));

	final Rule ATOM = Terminal("atom");

	final Rule CLOSE_RETARGET = Terminal("close_retarget");
	final Rule FAR_RETARGET = Terminal("far_retarget");
	final Rule CLOSE_NORETARGET = Terminal("close_noretarget");
	final Rule FAR_NORETARGET = Terminal("far_noretarget");
	final Rule COVER = Terminal("hamming_cover");

	// -------------------------------------------------------------------------
	// Keywords and terminals
	// -------------------------------------------------------------------------
	@SuppressNode
	@DontLabel
	Rule Keyword(String keyword) {
		return Terminal(keyword, LetterOrDigit());
	}

	@SuppressNode
	@DontLabel
	Rule Terminal(String string) {
		return Sequence(string, Space()).label('\'' + string + '\'');
	}

	@SuppressNode
	@DontLabel
	Rule Terminal(String string, Rule mustNotFollow) {
		return Sequence(string, TestNot(mustNotFollow), Space()).label('\'' + string + '\'');
	}

	/**
	 * @return [0-9]
	 */
	Rule Digit() {
		return CharRange('0', '9');
	}

	/**
	 * @return [a-z|A-Z|0-9|_|$]+
	 */
	@MemoMismatches
	Rule LetterOrDigit() {
		return FirstOf(CharRange('a', 'z'), CharRange('A', 'Z'), CharRange('0', '9'), '_', '$');
	}

	Rule NotSpace() {
		return NoneOf(" \n\r\t()[]{}");
	}

	Rule FilePathChar() {
		return Sequence(TestNot(AnyOf("\"\n\r")), ANY);
	}

	// -------------------------------------------------------------------------
	// Helper methods
	// -------------------------------------------------------------------------
	final Integer popInt() {
		return (Integer) pop();
	}

	final String popString() {
		return (String) pop();
	}
	final String peekString() {
		return (String) peek();
	}

	final Boolean popBool() {
		return (Boolean) pop();
	}

	final Options popOptions() {
		return (Options) pop();
	}

	final Tuple popTuple() {
		return (Tuple) pop();
	}

	final TupleSet popTupleSet() {
		return (TupleSet) pop();
	}

	final Relation popRelation() {
		return (Relation) pop();
	}

	final Expression popExpr() {
		return (Expression) pop();
	}

	
	final IntExpression popIntExpr() {
		return (IntExpression) pop();
	}

	final Formula popFormula() {
		return (Formula) pop();
	}

	final Decls popDecls() {
		return (Decls) pop();
	}

	final Multiplicity popMult() {
		return (Multiplicity) pop();
	}

	final StringDefEnv popEnv() {
		return (StringDefEnv) pop();
	}

	final List popList() {
		return (List) pop();
	}

	final Integer popInteger() {
		return (Integer) pop();
	}

	final Decl popDecl() {
		return (Decl) pop();
	}

	final StringDefEnv peekEnv() {
		return (StringDefEnv) peek();
	}

	final Multiplicity peekMult() {
		return (Multiplicity) peek();
	}

	final Expression peekExpr() {
		return (Expression) peek();
	}

	final Options peekOptions() {
		return (Options) peek();
	}

	/**
	 * Returns the current lexical environment, which is the first environment
	 * object from the top the stack, or {@code this.builder.global()} is there is
	 * no environment on the stack.
	 *
	 * @return current lexical environment
	 */
	final StringDefEnv env() {
		for (Object val : getContext().getValueStack()) {
			if (val instanceof StringDefEnv)
				return (StringDefEnv) val;
		}
		return currentProblem.env();
	}
}


