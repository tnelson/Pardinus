package kodkod.examples.pardinus.target;
import java.util.Arrays;
import java.util.List;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;


/* 
  ==================================================
    kodkod formula: 
  ==================================================
    (all this: this/Node | 
      (this . this/Node.adj) in this/Node) && 
    (this/Node.adj . univ) in this/Node && 
    (all this: this/Node | 
      one (this . this/Node.color) && 
      (this . this/Node.color) in this/Color) && 
    (this/Node.color . univ) in this/Node && 
    (all x: this/Node, y: this/Node | 
      (x in (y . (^this/Node.adj + (iden & ((ints + String + this/Node + 
       this/Color) -> univ)))) && 
       y in (x . (^this/Node.adj + (iden & ((ints + String + this/Node + 
       this/Color) -> univ))))) <=> 
      (x . this/Node.color) = (y . this/Node.color)) && 
    Int/next = Int/next && 
    seq/Int = seq/Int && 
    String = String && 
    this/Node = this/Node && 
    this/Color = this/Color && 
    this/Node.adj = this/Node.adj && 
    this/Node.color = this/Node.color
  ==================================================
*/
public final class Colors {

public static void main(String[] args) throws Exception {

Relation x0 = Relation.nary("Int/next", 2);
Relation x1 = Relation.unary("seq/Int");
Relation x2 = Relation.unary("String");
Relation x3 = Relation.unary("this/Node");
Relation x4 = Relation.unary("this/Color");
Relation x5 = Relation.nary("this/Node.adj", 2);
Relation x6 = Relation.nary("this/Node.color", 2);

List<String> atomlist = Arrays.asList(
 "Color$0", "Node$0", "unused0", "unused1", "unused2",
 "unused3"
);

Universe universe = new Universe(atomlist);
TupleFactory factory = universe.factory();
Bounds bounds = new Bounds(universe);

TupleSet x0_upper = factory.noneOf(2);
bounds.boundExactly(x0, x0_upper);

TupleSet x1_upper = factory.noneOf(1);
bounds.boundExactly(x1, x1_upper);

TupleSet x2_upper = factory.noneOf(1);
bounds.boundExactly(x2, x2_upper);

TupleSet x3_upper = factory.noneOf(1);
x3_upper.add(factory.tuple("unused0"));
x3_upper.add(factory.tuple("unused1"));
x3_upper.add(factory.tuple("Node$0"));
bounds.bound(x3, x3_upper);

TupleSet x4_upper = factory.noneOf(1);
x4_upper.add(factory.tuple("unused2"));
x4_upper.add(factory.tuple("unused3"));
x4_upper.add(factory.tuple("Color$0"));
bounds.bound(x4, x4_upper);

TupleSet x5_upper = factory.noneOf(2);
x5_upper.add(factory.tuple("unused0").product(factory.tuple("unused0")));
x5_upper.add(factory.tuple("unused0").product(factory.tuple("unused1")));
x5_upper.add(factory.tuple("unused0").product(factory.tuple("Node$0")));
x5_upper.add(factory.tuple("unused1").product(factory.tuple("unused0")));
x5_upper.add(factory.tuple("unused1").product(factory.tuple("unused1")));
x5_upper.add(factory.tuple("unused1").product(factory.tuple("Node$0")));
x5_upper.add(factory.tuple("Node$0").product(factory.tuple("unused0")));
x5_upper.add(factory.tuple("Node$0").product(factory.tuple("unused1")));
x5_upper.add(factory.tuple("Node$0").product(factory.tuple("Node$0")));
bounds.bound(x5, x5_upper);

TupleSet x6_upper = factory.noneOf(2);
x6_upper.add(factory.tuple("unused0").product(factory.tuple("unused2")));
x6_upper.add(factory.tuple("unused0").product(factory.tuple("unused3")));
x6_upper.add(factory.tuple("unused0").product(factory.tuple("Color$0")));
x6_upper.add(factory.tuple("unused1").product(factory.tuple("unused2")));
x6_upper.add(factory.tuple("unused1").product(factory.tuple("unused3")));
x6_upper.add(factory.tuple("unused1").product(factory.tuple("Color$0")));
x6_upper.add(factory.tuple("Node$0").product(factory.tuple("unused2")));
x6_upper.add(factory.tuple("Node$0").product(factory.tuple("unused3")));
x6_upper.add(factory.tuple("Node$0").product(factory.tuple("Color$0")));
bounds.bound(x6, x6_upper);


Variable x10=Variable.unary("this");
Decls x9=x10.oneOf(x3);
Expression x12=x10.join(x5);
Formula x11=x12.in(x3);
Formula x8=x11.forAll(x9);
Expression x14=x5.join(Expression.UNIV);
Formula x13=x14.in(x3);
Variable x18=Variable.unary("this");
Decls x17=x18.oneOf(x3);
Expression x21=x18.join(x6);
Formula x20=x21.one();
Formula x22=x21.in(x4);
Formula x19=x20.and(x22);
Formula x16=x19.forAll(x17);
Expression x24=x6.join(Expression.UNIV);
Formula x23=x24.in(x3);
Variable x28=Variable.unary("x");
Decls x27=x28.oneOf(x3);
Variable x30=Variable.unary("y");
Decls x29=x30.oneOf(x3);
Decls x26=x27.and(x29);
Expression x36=x5.closure();
Expression x42=Expression.INTS.union(x2);
Expression x41=x42.union(x3);
Expression x40=x41.union(x4);
Expression x39=x40.product(Expression.UNIV);
Expression x37=Expression.IDEN.intersection(x39);
Expression x35=x36.union(x37);
Expression x34=x30.join(x35);
Formula x33=x28.in(x34);
Expression x47=x5.closure();
Expression x49=x40.product(Expression.UNIV);
Expression x48=Expression.IDEN.intersection(x49);
Expression x46=x47.union(x48);
Expression x45=x28.join(x46);
Formula x44=x30.in(x45);
Formula x32=x33.and(x44);
Expression x51=x28.join(x6);
Expression x52=x30.join(x6);
Formula x50=x51.eq(x52);
Formula x31=x32.iff(x50);
Formula x25=x31.forAll(x26);
Formula x53=x0.eq(x0);
Formula x54=x1.eq(x1);
Formula x55=x2.eq(x2);
Formula x56=x3.eq(x3);
Formula x57=x4.eq(x4);
Formula x58=x5.eq(x5);
Formula x59=x6.eq(x6);
Formula x7=Formula.compose(FormulaOperator.AND, x8, x13, x16, x23, x25, x53, x54, x55, x56, x57, x58, x59);

Solver solver = new Solver();
solver.options().setSolver(SATFactory.DefaultSAT4J);
solver.options().setBitwidth(1);
solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
solver.options().setSymmetryBreaking(20);
solver.options().setSkolemDepth(0);
System.out.println("Solving...");
System.out.flush();
Solution sol = solver.solve(x7,bounds);
System.out.println(sol.toString());
}}
