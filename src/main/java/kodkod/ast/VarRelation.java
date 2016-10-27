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
package kodkod.ast;

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
public class VarRelation extends Relation {

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

	/**
	 * Returns a new variable relation with the given name and arity.
	 * @return {r: VarRelation | r.arity = arity && r.name = name }
	 * @throws IllegalArgumentException  arity < 1 
	 */
	public static VarRelation nary(String name, int arity) {
		return new VarRelation(name, arity);
	}

	/**
	 * Returns a new unary variable relation with the given name.  
	 * The effect of this method is the same as calling VarRelation.nary(name,1).
	 * @return {r: VarRelation | r.arity = 1 && r.name = name }
	 */
	public static VarRelation unary(String name) {
		return new VarRelation(name, 1);
	}

	/**
	 * Returns a new binary variable relation with the given name.  
	 * The effect of this method is the same as calling VarRelation.nary(name,2).
	 * @return {r: VarRelation | r.arity = 2 && r.name = name }
	 */
	public static VarRelation binary(String name) {
		return new VarRelation(name, 2);
	}

	/**
	 * Returns a new ternary variable relation with the given name.  
	 * The effect of this method is the same as calling VarRelation.nary(name,3).
	 * @return {r: VarRelation | r.arity = 3 && r.name = name }
	 */
	public static VarRelation ternary(String name) {
		return new VarRelation(name, 3);
	}

}