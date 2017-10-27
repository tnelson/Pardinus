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
import java.util.Arrays;
import java.util.Iterator;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.unbounded.ElectrodReader;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.ElectrodPrinter;
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
			String electrode = ElectrodPrinter.print(formula, bounds);
			PrintWriter writer;
			File dir = new File(options.uniqueName());
			if (!dir.exists()) dir.mkdir();
			String file = dir+"/"+dir+"-"+bounds.hashCode();
			writer = new PrintWriter(file+".elo", "UTF-8");
			writer.println(electrode);
			writer.close();
					
			ProcessBuilder builder = new ProcessBuilder("electrod","-vv",file+".elo");
			builder.redirectOutput(new File("electrod.log"));
			builder.redirectError(new File("electrod.log"));
			builder.environment().put("PATH", builder.environment().get("PATH")+":/usr/local/bin:.");
			Process p = builder.start();
			p.waitFor();

			// TODO: test return code of electrod and abort when failure
			
			ElectrodReader rd = new ElectrodReader(bounds);
			TemporalInstance res = null;
			try {
				res = rd.read(new File(file+".xml"));
			} catch (InvalidUnboundedSolution e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

			// TODO: get the stats from the header of the electrod solution
			
			if (res == null)
				return Solution.unsatisfiable(new Statistics(0, 0, 0, 0, 0), null);
			else
				return Solution.satisfiable(new Statistics(0, 0, 0, 0, 0), res);

		} catch (FileNotFoundException | UnsupportedEncodingException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return Solution.unsatisfiable(new Statistics(0, 0, 0, 0, 0), null);
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
		Solution[] ss = {s,Solution.unsatisfiable(new Statistics(0, 0, 0, 0, 0), null)};
		return Arrays.asList(ss).iterator();
	}

}
