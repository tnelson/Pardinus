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
package kodkod.engine;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.ElectrodProblemPrinter;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;

/**
 * A computational engine for solving unbounded temporal relational
 * satisfiability problems. Such a problem is described by a
 * {@link kodkod.ast.Formula formula} in first order temporal relational logic;
 * finite unbounded temporal {@link PardinusBounds bounds} on the value of each
 * {@link Relation relation} constrained by the respective formula; and a set of
 * {@link ExtendedOptions options}, although there are currently no
 * particular options for unbounded temporal solving.
 * 
 * <p>
 * An {@link ElectrodSolver} takes as input a relational problem and produces a
 * satisfying model or a {@link TemporalInstance temporal instance} of it, if
 * one exists.
 * </p>
 * 
 * @author Nuno Macedo // [HASLab] unbounded temporal model finding
 *
 */
public class ElectrodSolver implements UnboundedSolver<ExtendedOptions>, TemporalSolver<ExtendedOptions>, IterableSolver<PardinusBounds, ExtendedOptions> {

	private final ExtendedOptions options;

	/**
	 * Constructs a new Solver with the default options.
	 * 
	 * @ensures this.options' = new Options()
	 */
	public ElectrodSolver() {
		this.options = new ExtendedOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 * 
	 * @ensures this.options' = options
	 * @throws NullPointerException
	 *             options = null
	 */
	public ElectrodSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();
		this.options = options;
	}

	/**
	 * {@inheritDoc}
	 */
	public ExtendedOptions options() {
		return options;
	}

	/**
	 * {@inheritDoc}
	 */
	public Solution solve(Formula formula, PardinusBounds bounds) {
		try {
			String electrode = ElectrodProblemPrinter.print(formula, bounds);
			PrintWriter writer;
			DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss-"+bounds.hashCode());
			Date date = new Date();
			String file = "electrod"+dateFormat.format(date)+".elo";
			writer = new PrintWriter(file, "UTF-8");
			writer.println(electrode);
			writer.close();
//			Runtime.getRuntime().exec("electrod "+file).waitFor();
			TemporalInstance res = ElectrodProblemReader.read(bounds, new File("electrod.xml"));
			
		} catch (FileNotFoundException | UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
//		} catch (InterruptedException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
//		} catch (InterruptedException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
		}
		return Solution.unsatisfiable(null, null);
	}

	/**
	 * {@inheritDoc}
	 */
	public void free() {
		// TODO Auto-generated method stub

	}

	@Override
	public Iterator<Solution> solveAll(Formula formula, PardinusBounds bounds) {
		Solution s = solve(formula,bounds);
		Set<Solution> st = new HashSet<Solution>(Arrays.asList(s));
		return st.iterator();
	}

}
