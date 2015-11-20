package kkpartition.examples;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kkpartition.MProblem;
import kkpartition.PProblem;
import kkpartition.ParallelSolver;
import kkpartition.PartitionModel;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public final class RunTests {

	final static Solver solver = new Solver();
	final static ParallelSolver psolver = new ParallelSolver(solver);
	
	final static Map<Integer,List<PProblem>> stats = new HashMap<Integer,List<PProblem>> ();
	
	static PProblem solution = null;

	static boolean glucose, minisat, plingling;
	static boolean batch, sequential, parallel, hybrid, incremental;
	static int tries;
	
	static private StringBuilder log = new StringBuilder();
	
	static private PrintWriter writer;

	/**
	 * @throws UnsupportedEncodingException 
	 * @throws FileNotFoundException 
	 */
	public static void main(String[] args) throws FileNotFoundException, UnsupportedEncodingException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter("log.txt", "UTF-8");
		
		tries = Integer.valueOf(args[0]);
		
		glucose = opts.contains("-gl");
		minisat = opts.contains("-ms");
		plingling = opts.contains("-pl");

		batch = opts.contains("-b");
		sequential = opts.contains("-s");
		parallel = opts.contains("-p");
		hybrid = opts.contains("-h");
		incremental = opts.contains("-i");

		boolean ring = opts.contains("--ring");
		boolean handshake = opts.contains("--handshake");
		boolean hotel = opts.contains("--hotel");
		boolean file = opts.contains("--file");

		if (ring) runRing();
		if (handshake) runHandshake();
		if (hotel) runHotel();
		if (file) runFileSystem();
	}

	/**
	 * Given a partitioned model, runs the model under all considered parameters.
	 * @param model
	 * @param sym
	 */
	private static void run_tests(PartitionModel model, int sym) {
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		solver.options().setBitwidth(model.getBitwidth());
		solver.options().setSymmetryBreaking(sym);

		// warm up
//		for (int i = 0; i<30; i++)
//			solver.solve(f1, b1);

		// run under MiniSat in batch, sequential and parallel mode
		if (minisat) {
			solver.options().setSolver(SATFactory.MiniSat);
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			if (sequential)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(1);
					psolver.options().setHybrid(false);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			if (parallel)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(4);
					psolver.options().setHybrid(false);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}	
			if (hybrid)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(3);
					psolver.options().setHybrid(true);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}	
		}
		
		// run under Glucose in batch, sequential and parallel mode
		if (glucose) {
			solver.options().setSolver(SATFactory.Glucose);
			if (incremental)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					go_incremental(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			flush();
			if (sequential)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(1);
					psolver.options().setHybrid(false);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			flush();
			if (parallel)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(4);
					psolver.options().setHybrid(false);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
					flush();
				}	
			flush();
			if (hybrid)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(3);
					psolver.options().setHybrid(true);
					solution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}	
			flush();
		}
		
		// run under plingeling in batch
		if (plingling) {
			solver.options().setSolver(SATFactory.plingeling());
			if (batch)
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				go_batch(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				log.append((t2-t1));
				log.append("\t");
			}
		}
		
		log.append(solution.sat()?"S":"U");
		log.append("\t");
		log.append(getConfigNum(psolver));
		log.append("\t");
		log.append(getGenTime(psolver));
		log.append("\t");
		
		flush();
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	private static long getGenTime(ParallelSolver psolver2) {
		long counter = 0;
		for (PProblem p : psolver2.manager().solutions())
			if (p instanceof MProblem) counter = counter + ((MProblem) p).getConfigTime();
		return counter;
	}

	private static int getConfigNum(ParallelSolver psolver2) {
		int counter = psolver2.manager().solutions().size();
		if (!(psolver2.manager().solutions().get(psolver2.manager().solutions().size()-1) instanceof MProblem))
			counter = -counter;
		return counter;
	}

	/**
	 * Solves the problem under standard Kodkod (i.e., batch mode).
	 * @param b1
	 * @param b2
	 * @param f1
	 * @param f2
	 * @return 
	 */
	private static Solution go_batch(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return solver.solve(f1.and(f2), b3);
	}

	private static Solution go_incremental(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		IncrementalSolver isolver = IncrementalSolver.solver(solver.options());

		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		isolver.solve(f1,b3);
		b3.relations().clear();
		return isolver.solve(f2,b3);

//		isolver.solve(f1,b1);
//		return isolver.solve(f2,b2);
	}

	private static void printConfigs() {
		for (Integer i : stats.keySet()) {
			for (PProblem p : stats.get(i))
				System.out.println(p.toString());
			System.out.println();
		}		
	}

	/**
	 * Tests the performance of all variants of the Ring example.
	 */
	private static void runRing() {
		
		log.append("FC10\n");
		for (int i = 1; i <= 3; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,true,false,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FL10\n");
		for (int i = 1; i <= 7; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,true,true,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FS10\n");
		for (int i = 1; i <= 8; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,false,true,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("VC10\n");
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,true,false,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("VL10\n");
		for (int i = 1; i <= 6; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,true,true,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("VS10\n");
		for (int i = 1; i <= 7; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,10,false,true,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FC20\n");
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,false,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FL20\n");
		for (int i = 5; i <= 5; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,true,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FS20\n");
		for (int i = 1; i <= 8; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,false,true,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();
		
		log.append("VC20\n");
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,false,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs(); 
		
		log.append("VL20\n");
		for (int i = 1; i <= 6; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,true,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("VS20\n");
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new RingP(new Object[]{i,20,false,true,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
//		printConfigs();
	}

	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() {
		log.append("Intervenes10\n"); 
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new HotelP(new Object[]{i,10,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("NoIntervenes10\n"); 
		for (int i = 1; i <= 6; i ++) {
			log.append(i+"\t");
			run_tests(new HotelP(new Object[]{i,10,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();
		
		log.append("Intervenes20\n"); 
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new HotelP(new Object[]{i,20,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("NoIntervenes20\n"); 
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new HotelP(new Object[]{i,20,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();
	}
	
	/**
	 * Tests the performance of all variants of the Handshake example.
	 */
	private static void runHandshake() {
		
		log.append("FI\n"); 
		for (int i = 3; i <= 14; i ++) {
			log.append(i+"\t");
			run_tests(new HandshakeP(new Object[]{false,true,i}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();
		
		log.append("VI\n"); 
		for (int i = 3; i <= 14; i ++) {
			log.append(i+"\t");
			run_tests(new HandshakeP(new Object[]{true,true,i}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("FT\n"); 
		for (int i = 3; i <= 14; i ++) {
			log.append(i+"\t");
			run_tests(new HandshakeP(new Object[]{false,false,i}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("VT\n"); 
		for (int i = 3; i <= 14; i ++) {
			log.append(i+"\t");
			run_tests(new HandshakeP(new Object[]{true,false,i}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

	}

	private static void runFileSystem() {
		log.append("Buggy\n"); 
		for (int i = 2; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new FilesystemP(new Object[]{i,true}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();

		log.append("Correct\n"); 
		for (int i = 1; i <= 10; i ++) {
			log.append(i+"\t");
			run_tests(new FilesystemP(new Object[]{i,false}),20);
			log.append("\n");
			stats.put(i, psolver.manager().solutions());
		}
		log.append("\n");
//		printConfigs();
		
	}
	

}