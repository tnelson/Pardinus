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
package kodkod.engine.decomp;

import java.util.Iterator;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Formula;
import kodkod.ast.NaryFormula;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.config.DecomposedOptions;

/**
 * @author Nuno Macedo // [HASLab] decomposed model finding
 */
public class DecompFormulaSlicer {

	public final Formula f1;
	public final Formula f2;
	
	public DecompFormulaSlicer(Formula formula, DecomposedOptions<?> options) {
		// TODO: allow different slicing modes on options
		if (formula instanceof BinaryFormula && ((BinaryFormula) formula).op() == FormulaOperator.AND) {
			f1 = ((BinaryFormula) formula).left();
			f2 = ((BinaryFormula) formula).right();
		} else if (formula instanceof NaryFormula && ((NaryFormula) formula).op() == FormulaOperator.AND) {
			Iterator<Formula> it = ((NaryFormula) formula).iterator();
			f1 = it.next();
			Formula aux = Formula.TRUE;
			while (it.hasNext())
				aux = aux.and(it.next());
			f2 = aux;
		} else if (formula == Formula.FALSE){
			f1 = formula;
			f2 = Formula.FALSE;
		} else {
			f1 = formula;
			f2 = formula;
		}

	}
}
