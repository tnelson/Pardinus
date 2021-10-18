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
package kodkod.examples.alloy;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import kodkod.util.nodes.Nodes;
import kodkod.util.nodes.PrettyPrinter;

/**
 * Encodes the hotel example.
 *
 * @author Emina Torlak
 */
public final class Resolution {

  private final Relation neg, lits;
  private final Relation sources, resolvents, edges;

  private final Relation Boolean_;
  private final Relation True, False, Literal, Clause, Conflict, Refutation, Instance;

  private final Relation clauses, assign;

  /**
   * Constructs a new instance of the resolution problem.
   */
  public Resolution() {
    this.Boolean_ = Relation.unary("Boolean");

    this.True = Relation.unary("True");
    this.False = Relation.unary("False");
    this.Literal = Relation.unary("Literal");
    this.Clause = Relation.unary("Clause");
    this.Conflict = Relation.unary("Conflict");
    this.Refutation = Relation.unary("Refutation");
    this.Instance = Relation.unary("Instance");

    this.sources = Relation.binary("sources");
    this.resolvents = Relation.binary("resolvents");
    this.clauses = Relation.binary("clauses");
    this.neg = Relation.binary("neg");
    this.lits = Relation.binary("lits");

    this.edges = Relation.ternary("edges");
    this.assign = Relation.ternary("assign");
  }

  /**
   * Ensures that there are only one of True, False, Conflict sigs.
   * @return A Formula ensuring that there is only one True, one False, one Conflict sig.
   */
  public Formula oneSigEnforcement() {
    final List<Formula> invs = new ArrayList<Formula>();
    invs.add(True.one());
    invs.add(False.one());
    invs.add(Conflict.one());
    return Formula.and(invs);
  }

  /**
   * Ensures that each Literal has exactly one negation.
   * @return a Formula that enforces that each Literal will have exactly one negation.
   */
  public Formula oneNegPerLiteral() {
    final Variable l = Variable.unary("l");
    return (l.join(neg).one()).forAll(l.oneOf(Literal))
        .and(Literal.join(neg).eq(Literal));
  }

  /**
   * Represents the predicate saying that negation is both symmetric and irreflexive.
   * @return a Formula representing the above predicate.
   */
  public Formula negationIsSymmetricAndIrreflexive() {
    final List<Formula> invs = new ArrayList<Formula>();
    invs.add(neg.eq(neg.transpose()));
    invs.add((Expression.IDEN.intersection(neg)).no());
    return Formula.and(invs);
  }

  /**
   * Represents the predicate specifying that Conflict clauses have no literals.
   * @return a Formula representing the above predicate.
   */
  public Formula conflictWellformedness() {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable c = Variable.unary("c");
    final Formula f0 = (c.join(lits)).no();
    invs.add(f0.forAll(c.oneOf(Conflict)));

    return Formula.and(invs);
  }

  /**
   * Represents the predicate specifying that clauses that aren't conflicts
   * can't be empty.
   * @return a Formula representing the above predicate.
   */
  public Formula nonConflictClausesAreNonEmpty() {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable c = Variable.unary("c");
    final Formula f0 = (c.join(lits)).some();
    invs.add(f0.forAll(c.oneOf(Clause.difference(Conflict))));

    return Formula.and(invs);
  }

  /**
   * Represents the predicate specifying that a clause cannot contain both
   * a literal and its negation.
   * @return a Formula representing the above predicate.
   */
  public Formula noClauseHasLiteralAndNegation() {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable c = Variable.unary("c");
    final Formula f0 = (c.join(lits).intersection(c.join(lits).join(neg))).no();
    invs.add(f0.forAll(c.oneOf(Clause)));

    return Formula.and(invs);
  }

  /**
   * Represents a function that represents a valid resolution step.
   * @return a Formula representing the above function.
   */
  public Formula resolve(Expression c1, Expression c2, Expression r) {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable x = Variable.unary("x");
    final Formula f0 = r.join(lits).eq((c1.join(lits).union(c2.join(lits)))
        .difference(x.union(x.join(neg))));
    invs.add(f0.forAll(x.oneOf(c1.join(lits).intersection(c2.join(lits).join(neg)))));

    return Formula.and(invs);
  }

  /**
   * Represents a predicate that specifies the conditions for a Refutation
   * to be well-formed.
   * @return a Formula representing the above predicate.
   */
  public Formula refutationWellFormedness() {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable r = Variable.unary("r");
    final Variable c = Variable.unary("c");
    final Variable n1 = Variable.unary("n1");
    final Variable n2 = Variable.unary("n2");
    final Variable res = Variable.unary("res");

    final Formula f0 = r.join(sources).some().and((r.join(sources).intersection(Conflict)).no());
    invs.add(f0.forAll(r.oneOf(Refutation)));

    final Formula f1 = r.join(edges).eq((r.join(sources).union(r.join(resolvents)))
        .product(r.join(resolvents)));
    invs.add(f1.forAll(r.oneOf(Refutation)));

    final Formula f2 = ((Expression.IDEN).intersection(r.join(edges).reflexiveClosure())).no();
    invs.add(f2.forAll(r.oneOf(Refutation)));

    final Formula f30 = (r.join(edges).join(res)).no();
    final Formula f31 = f30.comprehension(res.oneOf(r.join(resolvents))).no();
    invs.add(f31.forAll(r.oneOf(Refutation)));

    final Formula f40 = c.in(r.join(resolvents));
    final Formula f41 = f40.forAll(c.oneOf(Conflict));
    invs.add(f41.forAll(r.oneOf(Refutation)));

    final Formula f50 = (n1.union(n2)).product(res).in(r.join(edges))
        .iff(resolve(n1, n2, res));
    final Formula f51 = f50.forAll(res.oneOf(r.join(resolvents)));
    final Formula f52 = f51.forAll(res.oneOf(r.join(sources).union(r.join(resolvents))));
    final Formula f53 = f52.forAll(res.oneOf(r.join(sources).union(r.join(resolvents))));
    invs.add(f53.forAll(r.oneOf(Refutation)));

    return Formula.and(invs);
  }

  /**
   * Represents a predicate that specifies the conditions for an Instance
   * to be well-formed.
   * @return a Formula representing the above predicate.
   */
  public Formula instanceWellFormedness() {
    final List<Formula> invs = new ArrayList<Formula>();
    final Variable i = Variable.unary("i");
    final Variable c = Variable.unary("c");
    final Variable lit = Variable.unary("lit");

    final Formula f1 = i.join(clauses).some();
    invs.add(f1.forAll(i.oneOf(Instance)));

    final Formula f2 = Literal.join(i.join(assign)).lone();
    invs.add(f2.forAll(i.oneOf(Instance)));

    final Formula f30 = i.join(lit.join(assign))
        .eq(Boolean_.difference(i.join((lit.join(neg)).join(assign))));
    final Formula f301 = f30.forAll(lit.oneOf(i.join(clauses).join(lits)));
    final Formula f31 = True.in(i.join(c.join(lits)).join(assign));
    final Formula f311 = f31.forAll(c.oneOf(i.join(clauses)));
    final Formula f32 = f301.and(f311);
    invs.add(f32.forAll(i.oneOf(Instance)));

    return Formula.and(invs);
  }

  /**
   * Returns the conjunction of all invariants.
   * @return conjunction of all invariants.
   */
  public Formula invariants() {
    final List<Formula> invs = new ArrayList<Formula>();

    return Formula.and(invs);
  }

  /**
   * Returns bounds for the given number of Literal, Clause, Refutation, Instance.
   * @return bounds for the given scopes.
   */
  public PardinusBounds bounds(int l, int c, int r, int in) {
    final Relation[] tops = { Literal, Clause, Refutation, Instance };
    final int[] scopes = { l, c, r, in};

    final List<String> atoms = new ArrayList<String>();
    for(int i = 0; i < tops.length; i++) {
      Relation top = tops[i];
      for(int j = 0, scope = scopes[i]; j < scope; j++)
        atoms.add(top.name() + j);
    }

    final Universe u = new Universe(atoms);
    final TupleFactory f = u.factory();
    final PardinusBounds b = new PardinusBounds(u);

    for(int i = 0 ; i < tops.length; i++) {
      Relation top = tops[i];
      b.bound(top, f.range(f.tuple(top.name()+0), f.tuple(top.name()+(scopes[i]-1))));
    }

    b.bound(neg, b.upperBound(Literal).product(b.upperBound(Literal)));
    b.bound(lits, b.upperBound(Clause).product(b.upperBound(Literal)));
    b.bound(sources, b.upperBound(Refutation).product(b.upperBound(Clause)));
    b.bound(resolvents, b.upperBound(Refutation).product(b.upperBound(Clause)));
    b.bound(edges, b.upperBound(Refutation).product(b.upperBound(Clause)).product(b.upperBound(Clause)));
    b.bound(clauses, b.upperBound(Instance).product(b.upperBound(Clause)));
    b.bound(assign, b.upperBound(Instance).product(b.upperBound(Literal)).product(b.upperBound(Boolean_)));

    b.bound(Conflict, b.upperBound(Clause));

    return b;
  }
  /**
   * Returns bounds for the given scope.
   * @return bounds for the given scope.
   */
  public PardinusBounds bounds(int n) {
    return bounds(n, n, n, n);
  }

  private static void usage() {
    System.out.println("java examples.Resolution [scope]");
    System.exit(1);
  }

  private static void checkMinimal(Set<Formula> core, Bounds bounds) {
    System.out.print("checking minimality ... ");
    final long start = System.currentTimeMillis();
    final Set<Formula> minCore = new LinkedHashSet<Formula>(core);
    Solver solver = new Solver();
    solver.options().setSolver(SATFactory.MiniSat);
    for(Iterator<Formula> itr = minCore.iterator(); itr.hasNext();) {
      Formula f = itr.next();
      Formula noF = Formula.TRUE;
      for( Formula f1 : minCore ) {
        if (f!=f1)
          noF = noF.and(f1);
      }
      if (solver.solve(noF, bounds).instance()==null) {
        itr.remove();
      }
    }
    final long end = System.currentTimeMillis();
    if (minCore.size()==core.size()) {
      System.out.println("minimal (" + (end-start) + " ms).");
    } else {
      System.out.println("not minimal (" + (end-start) + " ms). The minimal core has these " + minCore.size() + " formulas:");
      for(Formula f : minCore) {
        System.out.println(" " + f);
      }
//			Solution sol = problem.solver.solve(Formula.and(minCore), problem.bounds);
//			System.out.println(sol);
//			sol.proof().highLevelCore();
    }
  }

  /**
   * Usage: java examples.Resolution [scope]
   */
  public static void main(String[] args) {
    if (args.length < 1) {
      usage();
    }

    try {
      final int n = Integer.parseInt(args[0]);
      if (n < 1)
        usage();
      final Hotel model = new Hotel();
      final Solver solver = new Solver();
      solver.options().setSolver(SATFactory.MiniSatProver);
      solver.options().setLogTranslation(1);

      final Formula f = model.checkNoBadEntry();
      final Bounds b = model.bounds(n);

      //System.out.println(PrettyPrinter.print(f, 2, 100));

      final Solution sol = solver.solve(f, b);
      System.out.println(sol);

      if (sol.instance()==null) {
        final Proof proof = sol.proof();
        System.out.println("top-level formulas: " + proof.log().roots().size());
        System.out.println("initial core: " + proof.highLevelCore().size());
        System.out.print("\nminimizing core ... ");
        final long start = System.currentTimeMillis();
        proof.minimize(new RCEStrategy(proof.log()));
        final Set<Formula> core = Nodes.minRoots(f, proof.highLevelCore().values());
        final long end = System.currentTimeMillis();
        System.out.println("done (" + (end-start) + " ms).");
        System.out.println("minimal core: " + core.size());
        for(Formula u : core) {
          System.out.println(PrettyPrinter.print(u, 2, 100));
        }
        checkMinimal(core, b);
      } else {
        System.out.println(sol);
      }
    } catch (NumberFormatException nfe) {
      System.out.println("Number format exception!");
      usage();
    }
  }
}
