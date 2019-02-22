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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.ast;

import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.Quantifier;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/** 
 * A relation is a leaf expression.  
 * Two relations are the same if and only if they
 * refer to the same object.  That is, r1.equals(r2) <=> r1 == r2.  Each
 * variable has a name, which is a comment for the purpose of 
 * printing, viewing, etc.  The name has no meaning otherwise.
 * 
 * <p>Four methods for creating commonly used predicates over binary relations
 * are provided: {@link #function(Expression, Expression)}, {@link #partialFunction(Expression, Expression)},
 * {@link #acyclic()}, and {@link #totalOrder(Relation, Relation, Relation)}.  Using
 * these methods to generate desired predicates will result in faster constraint solving
 * than creating the same predicates via other API calls.</p> 
 * 
 * @specfield name: String
 * @specfield arity: int
 * @invariant no children
 * @author Emina Torlak 
 * @modified Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class Relation extends LeafExpression {
	/**
	 * Constructs a relation with the specified name and arity.
	 * @ensures this.name' = name && this.arity' = arity 
	 * @throws IllegalArgumentException  arity < 1 
	 */
	// [HASLab] protected constructor
	protected Relation(String name, int arity) {  
		super(name,arity);
	}
	
	/**
	 * Returns a new relation with the given name and arity.
	 * @return {r: Relation | r.arity = arity && r.name = name }
	 * @throws IllegalArgumentException  arity < 1 
	 */
	public static Relation nary(String name, int arity) {
		return new Relation(name,arity);
	}	

	/**
	 * Returns a new unary relation with the given name.  
	 * The effect of this method is the same as calling Relation.nary(name,1).
	 * @return {r: Relation | r.arity = 1 && r.name = name }
	 */
	public static Relation unary(String name) {
		return new Relation(name,1);
	}
	
	/**
	 * Returns a new binary relation with the given name.
	 * The effect of this method is the same as calling Relation.nary(name,2). 
	 * @return {r: Relation | r.arity = 2 && r.name = name }
	 */
	public static Relation binary(String name) {
		return new Relation(name, 2);
	}
	
	/**
	 * Returns a ternary relation with the specified name.
	 * @return {r: Relation | r.name = name && r.arity = 3}
	 */
	public static Relation ternary(String name) {
		return new Relation(name,3);
	}
	
    /**
     * TODO
     *
     * @param name
     * @return
     */
    public static VarRelation variable(String name,int arity) {
        return new VarRelation(name, arity);
    }
    
    /**
     * TODO
     *
     * @param name
     * @return
     */
    public static VarRelation unary_variable(String name) {
        return new VarRelation(name, 1);
    }

    /**
     * TODO
     *
     * @param name
     * @return
     */
    public static VarRelation binary_variable(String name) {
        return new VarRelation(name, 2);
    }

    /**
     * TODO
     *
     * @param name
     * @return
     */
    public static AtomRelation atom(String name) {
        return new AtomRelation(name, 1);
    }
	
    public static Relation skolem(String name, int arity, Variable forVariable, Decl decl, Quantifier quant) {
        return new SkolemRelation(name, arity, forVariable, decl, quant);
    }
    
    public boolean isAtom() {
        return false;
    }
    
    public boolean isSkolem() {
        return false;
    }
    
    public Variable getSkolemVar() {
        return null;
    }

    public Decl getSkolemVarDecl() {
        return null;
    }

    public Expression getSkolemVarDomain() {
        return null;
    }

    public Quantifier getSkolemVarQuant() {
        return null;
    }
    
    public boolean isVariable() {
        return false;
    }
    
    public Relation getExpansion() {
        return null;
    }
    
	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Expression#accept(kodkod.ast.visitor.ReturnVisitor)
	 */
	public <E, F, D, I> E accept(ReturnVisitor<E, F, D, I> visitor) {
		return visitor.visit(this);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.ast.Node#accept(kodkod.ast.visitor.VoidVisitor)
	 */
	public void accept(VoidVisitor visitor) {
		visitor.visit(this);
	}

    
	/**
     * Returns a formula stating that this relation is acyclic.
     * @return {f: Formula | f <=> no ^this & iden}
     * @throws IllegalArgumentException  this.arity != 2
     */
    public Formula acyclic() {
    		return new RelationPredicate.Acyclic(this);
    }
    
    /**
     * Returns a formula stating that this relation is a total function
     * with the specified domain and range.
     * @return {f: Formula | f <=> this in domain->range && all v: domain | one v.this }
     * @throws NullPointerException  domain = null || range = null
     * @throws IllegalArgumentException  domain.arity != 1 || range.arity != 1
     * @throws IllegalArgumentException  this.arity != 2
     */
    public Formula function(Expression domain, Expression range) {
    		return new RelationPredicate.Function(this, domain, Multiplicity.ONE, range);
    }
    
    /**
     * Returns a formula stating that this relation is a partial function
     * with the specified domain and range.
     * @return {f: Formula | f <=> this in domain->range && all v: domain | lone v.this }
     * @throws NullPointerException  domain = null || range = null
     * @throws IllegalArgumentException  domain.arity != 1 || range.arity != 1
     * @throws IllegalArgumentException  this.arity != 2
     */
    public Formula partialFunction(Expression domain, Expression range) {
    		return new RelationPredicate.Function(this, domain, Multiplicity.LONE, range);
    }
    
    /**
     * Returns a formula stating that this relation imposes a total ordering
     * over the atoms in the set <code>ordered</code>, and that thet first and
     * last elements in the ordering are given by the relations <code>first</code>
     * and <code>last</code>.
     * @return {f: Formula | f <=> one first && one last && last in ordered &&
     *                             no this.first && no last.this &&  
     *                             ordered = first.*this && 
     *                             all e: ordered - last | one e.this }
     * @throws NullPointerException  any of the arguments are null
     * @throws IllegalArgumentException  any of the argument relations' arities are greater than one
     * @throws IllegalArgumentException  this.arity != 2
     */
    public Formula totalOrder(Relation ordered, Relation first, Relation last) {
    		return new RelationPredicate.TotalOrdering(this, ordered, first, last);
    }

}

class AtomRelation extends Relation {

    public AtomRelation(String name, int arity) {
        super(name, arity);
    }

    @Override
    public boolean isAtom() {
        return true;
    }

    @Override
    public String toString() {
        return "$$" + name() + "$$";
    }
}

class SkolemRelation extends Relation {

    private final Variable   forVariable;
    private final Decl       skolemVarDecl;
    private final Quantifier quant;

    public SkolemRelation(String name, int arity, Variable forVariable, Decl decl, Quantifier quant) {
        super(name, arity);
        this.forVariable = forVariable;
        this.skolemVarDecl = decl;
        this.quant = quant;
    }

    @Override
    public boolean isSkolem() {
        return true;
    }

    @Override
    public final Variable getSkolemVar() {
        return forVariable;
    }

    @Override
    public final Decl getSkolemVarDecl() {
        return skolemVarDecl;
    }

    @Override
    public final Expression getSkolemVarDomain() {
        return skolemVarDecl.expression();
    }

    @Override
    public final Quantifier getSkolemVarQuant() {
        return quant;
    }
}

/**
 * An extension to regular {@link Relation relations} that can evolve in time.
 * At creation time, these variable relations also create a regular relation
 * that represent will represent its expansion with explicit time.
 * 
 * @see Relation
 * 
 * @specfield expanded: Relation
 * @invariant expanded.arity = this.arity + 1
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
class VarRelation extends Relation {

	public final Relation expanded;

	/**
	 * Constructs a variable relation with the specified name and arity, as well
	 * as its expanded version.
	 * @ensures this.name' = name && this.arity' = arity && expanded.arity = arity + 1
	 * @throws IllegalArgumentException
	 *             arity < 1
	 */
    public VarRelation(String name, int arity) {
        super(name, arity);
		expanded = Relation.nary(name, arity + 1);
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public Relation getExpansion() {
        return expanded;
    }

    @Override
    public String toString() {
        return name();
    }
}
