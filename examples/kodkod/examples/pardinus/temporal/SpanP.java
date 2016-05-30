package kodkod.examples.pardinus.temporal;


import kodkod.ast.*;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.ltl2fol.TemporalFormulaExtension;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.pardinus.decomp.DModel;
import java.util.ArrayList;
import java.util.List;


public class SpanP implements DModel {


    public Bounds bounds1(){
        return this.temporalFormula.getStaticBounds();
    }

    public Bounds bounds2(){
        return this.temporalFormula.getDynamicBounds();
    }

    public Formula partition1() {
        return this.temporalFormula.getStaticFormula();
    }

    public Formula partition2(){ return this.temporalFormula.getDynamicFormula(); }

    public int getBitwidth() {
        return 1;
    }



    final private Relation Root,Process_rem,Level,adjacent;
    final private Relation level_first,level_next,level_last;

    private int n_ps, n_ts;
    private Variant var;

    final private VarRelation level,parent,runs ;

    private TemporalFormulaExtension temporalFormula;


    public enum Variant {
        V1,
        V2,
        V3;
    }

    public SpanP( String args[]){

        Root = Relation.unary("this/Root");
        Process_rem = Relation.unary("this/Process remainder");
        Level = Relation.unary("this/Lvl");
        adjacent = Relation.nary("this/Process.adj", 2);
        level_first = Relation.unary("lo/Ord.First");
        level_next = Relation.nary("lo/Ord.Next", 2);
        level_last = Relation.unary("");

        runs = VarRelation.nary("this/State.runs", 1);
        level = VarRelation.nary("this/State.lvl", 2);
        parent = VarRelation.nary("this/State.parent", 2);


        n_ps = Integer.valueOf(args[0]);
        n_ts = Integer.valueOf(args[1]);
        var = Variant.valueOf(args[2]);

        Formula formula = finalFormula();
        Bounds var6 = bounds();
        temporalFormula = new TemporalFormulaExtension(formula, var6,n_ts);


    }


    public Formula staticPart() {
        Expression Process = Root.union(Process_rem);

        Formula x89=level_next.totalOrder(Level,level_first,level_last);
        Formula x90=adjacent.in(Process.product(Process));
        Formula decls = x89.and(x90);

        Expression x100=Expression.IDEN.intersection(Process.product(Process));
        Expression x99=x100.intersection(adjacent);
        Formula x98=x99.no();

        Formula x110=adjacent.transpose().in(adjacent);

        Expression x116=Expression.IDEN.intersection(Process.product(Process));
        Expression x114=adjacent.closure().union(x116);
        Expression x113=Root.join(x114);
        Formula x112=Process.in(x113);
        Formula processgraph = x112.and(x110).and(x98);

        return Formula.compose(FormulaOperator.AND, decls, processgraph);
    }

    private Formula TRNop(Expression p) {
        Formula x130=p.join(level).eq(p.join(level.post())); /*TEMPORAL OP*/
        Formula x136=p.join(parent).eq(p.join(parent.post()));/*TEMPORAL OP*/
        return x130.and(x136);
    }

    private Formula TRActPreConds(Expression p) {
        Formula x146=p.join(level).no();
        Formula x150=p.eq(Root);
        Formula x151=p.join(adjacent).join(level).some();
        Formula x149=x150.or(x151);
        return x146.and(x149);
    }

    private Formula TRAct(Expression p) {
        Formula x173=p.join(level).no();
        Formula x178=p.eq(Root);
        Formula x180=p.join(level.post()).eq(level_first);/*TEMPORAL OP*/
        Formula x184=p.join(parent.post()).no();/*TEMPORAL OP*/
        Formula x179=x180.and(x184);
        Formula x177=x178.implies(x179);
        Variable x191=Variable.unary("TRAct_adjProc");
        Formula x195=x191.join(level).some();
        Formula x198=p.join(level.post()).eq(x191.join(level).join(level_next));/*TEMPORAL OP*/
        Formula x202=p.join(parent.post()).eq(x191);/*TEMPORAL OP*/
        Formula x193=x195.and(x198).and(x202);
        Formula x189=x193.forSome(x191.oneOf(p.join(adjacent)));
        Formula x187=x178.not().implies(x189);
        return x173.and(x177).and(x187);
    }

    private Formula init() {
        Formula x156=level.no();
        Formula x158=parent.no();
        return x156.and(x158);
    }

    private Formula spanTreeAtState() {
        Expression Process = Root.union(Process_rem);

        Expression x233=parent;
        Expression x236=Expression.IDEN.intersection(Process.product(Process));
        Formula x230=Process.in(Root.join(x233.union(x236)));
        Variable x240=Variable.unary("acyclic_x");
        Formula x242=x240.in(x240.join(parent));
        Formula x241=x242.not();
        Formula x238=x241.forAll(x240.oneOf(Process));
        return x230.and(x238);
    }

    private Formula successfulRun() {
        Formula x229=spanTreeAtState();
        //Variable x249=Variable.unary("SuccessfulRun_s");
        //Formula x252=spanTreeAtState(x249);
        //Formula x251=x252.not();
        Formula x251=x229.not();
        Formula x247=x251.always();/*TEMPORAL OP*/
        return x229.and(x247);
    }

    public Formula temporalPart() {
        Expression Process = Root.union(Process_rem);

        // decls
        Variable x46=Variable.unary("v0");
        Formula x44=(x46.join(level)).lone().forAll(x46.oneOf(Process));
        Formula x36=x44.always();/*TEMPORAL OP*/

        Formula x56=level.in(Process.product(Level)).always();/*TEMPORAL OP*/

        Variable x69=Variable.unary("v2");
        Formula x67=(x69.join(parent)).lone().forAll(x69.oneOf(Process));
        Formula x59=x67.always();/*TEMPORAL OP*/

        Formula x57=parent.in(Process.product(Process)).always();/*TEMPORAL OP*/


        Formula decls = x36.and(x56).and(x59).and(x57);

        // trans if possible
        Variable x128=Variable.unary("SuccessfulRun_p");
        Formula x129=TRNop(x128);

        Formula x126=x129.forAll(x128.oneOf(Process));
        Variable x143=Variable.unary("SuccessfulRun_p");
        Formula x145=TRActPreConds(x143);
        Formula x144=x145.not();
        Formula x141=x144.forAll(x143.oneOf(Process));
        Formula x124=x126.implies(x141);
        Formula transifpossible=x124.always();/*TEMPORAL OP*/

        // legal trans
        Formula x155=init();
        Variable x166=Variable.unary("SuccessfulRun_p");
        Formula x169=x166.in(runs);
        Formula x172=TRAct(x166);
        Formula x205=TRNop(x166);
        Formula x171=x172.or(x205);
        Formula x168=x169.implies(x171);
        Formula x218=TRNop(x166);
        Formula x216=x169.not().implies(x218);
        Formula x167=x168.and(x216);
        Formula x164=x167.forAll(x166.oneOf(Process));
        Formula x160=x164.always();/*TEMPORAL OP*/;
        Formula legaltrans = x160.and(x155);

        Formula res = Formula.compose(FormulaOperator.AND, decls, transifpossible, legaltrans);

        if (var == Variant.V1)
            return res.and(successfulRun());
        else if (var == Variant.V2)
            return res.and(traceWithoutLoop());
        else
            return res.and(badLivenessTrace());

    }


    private Formula finalFormula(){
        return temporalPart().and(staticPart());
    }

    /*private Formula equivStates(Expression s, Expression s1) {
        Expression x109=s.join(level);
        Expression x110=s1.join(level);
        Formula x108=x109.eq(x110);
        Expression x112=s.join(parent);
        Expression x113=s1.join(parent);
        Formula x111=x112.eq(x113);
        return x108.and(x111);
    }*/

    private Formula traceWithoutLoop() {
        //Variable x101=Variable.unary("TraceWithoutLoop_s");
        // Variable x103=Variable.unary("TraceWithoutLoop_s'");
        // Formula x105=x101.eq(x103).not();

        // Formula x109=equivStates(x101, x103).not();

        //Formula x120=x103.in(x101.join(state_next.closure()));
        //Formula x123=x103.eq(x101.join(state_next)).not();
        // Formula x118=x120.and(x123);

        Variable x129=Variable.unary("PossTrans_p");
        Formula x130=TRAct(x129).or(TRNop(x129));

        Formula x127=x130.forAll(x129.oneOf(Process_rem.union(Root)));
        Formula x126=x127.not();
        Formula x117=x126;

        Formula x108=x117;
        Formula x104=x108;
        Formula x98=x104.always();/*TEMPORAL OP*/

        Formula x178=spanTreeAtState();
        Formula x177=x178.not();
        Formula x174=x177.always();/*TEMPORAL OP*/;
        return x98.and(x174);
    }

    private Formula badLivenessTrace() {

        //  Variable x101=Variable.unary("BadLivenessTrace_s");
        // Variable x103=Variable.unary("BadLivenessTrace_s'");
        //Formula x105=x101.eq(x103).not();
        // Formula x104=x105.and(equivStates(x101, x103));
        //Formula x98=x104.forSome(x101.oneOf(State).and(x103.oneOf(State)));

        Formula x118=spanTreeAtState();
        Formula x117=x118.not();
        Formula x114=x117.always();/*TEMPORAL OP*/

        return x114;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder("Span");
        sb.append("-");
        sb.append(n_ps);
        sb.append("-");
        sb.append(n_ts);
        return sb.toString();
    }




    /**
     * Returns a bounds for the given number of persons.
     *
     * @return a bounds for the given number of persons.
     */
    public Bounds bounds() {
        final List<Object> atoms = new ArrayList<Object>(2*n_ps);

        atoms.add("Root");
        for (int i = 1; i < n_ps; i++)
            atoms.add("Process" + i);

        for (int i = 0; i < n_ps; i++)
            atoms.add("Lvl" + i);

        Universe  u = new Universe(atoms);

        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        final TupleSet pb = f.range(f.tuple("Root"), f.tuple("Process"+ (n_ps-1)));
        final TupleSet rb = f.range(f.tuple("Process1"), f.tuple("Process"+ (n_ps - 1)));
        final TupleSet lb = f.range(f.tuple("Lvl0"), f.tuple("Lvl"+ (n_ps-1)));

        b.boundExactly(Root, f.setOf("Root"));
        b.boundExactly(Process_rem, rb);
        b.boundExactly(Level, lb);
        b.bound(adjacent, pb.product(pb));
        b.bound(runs, pb);
        b.bound(level, pb.product(lb));
        b.bound(parent, pb.product(pb));

        b.bound(level_first, lb);
        b.bound(level_next, lb.product(lb));
        b.bound(level_last, lb);

        return b;
    }



    @Override
    public String shortName() {
        // TODO Auto-generated method stub
        return null;
    }


    public static void main(String[] args) {
        SpanP model = new SpanP(new String[]{"2","9","V3"});
        Bounds b1 = model.temporalFormula.getStaticBounds();
        Bounds b2 = model.temporalFormula.getDynamicBounds();
        Formula f1 = model.temporalFormula.getStaticFormula();
        Formula f2 = model.temporalFormula.getDynamicFormula();

        Bounds b3 = b1.clone();
        for (Relation r : b2.relations()) {
            b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
        }
        Solver solver = new Solver();
        solver.options().setSolver(SATFactory.DefaultSAT4J);
        Solution sol = solver.solve(f1.and(f2), b3);

        System.out.println(f2);

        System.out.println(sol);
        return;
    }
}
