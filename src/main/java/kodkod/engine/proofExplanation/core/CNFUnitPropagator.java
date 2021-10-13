package kodkod.engine.proofExplanation.core;

import kodkod.ast.*;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.satlab.Clause;

import java.text.Normalizer;
import java.util.*;

public class CNFUnitPropagator extends AbstractReplacer {

  private CNFUnitPropagator(HashSet<Node> cached, HashSet<Node> ucached) {
    super(cached);
    this.ucached = ucached;
    this.ucache = new IdentityHashMap<Node,Node>(ucached.size());
  }

  protected final Map<Node,Node> ucache;
  protected final Set<Node> ucached;

  /**
   * Performs unit propagation with a given literal on a set of conjunctions, and returns
   *    the resulting set of modified Formulae.
   * @param conjunctionIter A iterator of Formulas representing the conjunctions to propagate on.
   * @param propLiteral A Formula representing the literal in reference during unit propagation.
   * @return A set of Formulas such that those containing the literal for unit propagation in the
   *    original set are not kept, and those containing the negation of the literal are
   *    removed from the formula.
   */
  public static Set<Formula> propagateOnConjunctionIter(Iterator<Formula> conjunctionIter, Formula propLiteral) {
    Set<Formula> returnSet = new HashSet<>();

    // TODO: simpler check that converts some to no and vice-versa instead of using not


    Formula negationCompFmla = propLiteral;
    if (propLiteral instanceof MultiplicityFormula) {
      negationCompFmla = ((MultiplicityFormula) propLiteral).getNegation();
    }
    /*
    if (propLiteral instanceof NotFormula) {
      NotFormula notLiteral = (NotFormula) propLiteral;
      negationCompFmla = notLiteral.formula();
    } else {
      negationCompFmla = propLiteral.not();
    }*/

    // HACK TO DEBUG
    //negationCompFmla = propLiteral.
    System.out.println(negationCompFmla);

    while (conjunctionIter.hasNext()) {
      Formula conjunction = conjunctionIter.next();
      Set<Formula> literalSet = convertConjunctionToLiteralSet(conjunction);
      System.out.println("Literals:");
      for (Formula literal : literalSet) {
        System.out.print(literal + "; ");
      }
      System.out.println();

      boolean literalsHaveNegation = false;
      for (Formula literal : literalSet) {
        System.out.println(literal.getClass());
        if (negationCompFmla.equals(literal)) {
          literalsHaveNegation = true;
          break;
        }
      }
      if (!literalSet.contains(propLiteral) && literalsHaveNegation) {
        literalSet.remove(negationCompFmla);
        Formula newConjunction = Formula.compose(FormulaOperator.OR, literalSet.toArray(new Formula[0]));
        returnSet.add(newConjunction);
      } else {
        returnSet.add(conjunction);
      }
      System.out.println("Set so far: ");
      for (Formula f : returnSet) {
        System.out.print(f + "; ");
      }
      System.out.println();
    }
    return returnSet;
  }

  /**
   * Converts a formula that is a conjunction of literals to a set of literals.
   * @param conjunction A Formula that is a conjunction, i.e. held together by `or`s.
   * @return A set of Formulas, each of which is a literal.
   */
  public static Set<Formula> convertConjunctionToLiteralSet(Formula conjunction) {
    Set<Formula> currSet = new HashSet<>();
    if (!(conjunction instanceof BinaryFormula)) {
      currSet.add(conjunction);
      return currSet;
    }
    BinaryFormula conjHalves = (BinaryFormula) conjunction;
    currSet.add(conjHalves.right());
    currSet.addAll(convertConjunctionToLiteralSet(conjHalves.left()));
    return currSet;
  }
}
