package kkpartition;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kkpartition.examples.HandshakeP;
import kkpartition.examples.HotelP;
import kkpartition.examples.RingP;
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
	
	static List<PProblem> solutions = null;

	/**
	 */
	public static void main(String[] args) {
//		runRing();
//		runHandshake();
		runHotel();
	}

	/**
	 * Given a partitioned model, runs the model under all considered parameters.
	 * @param model
	 * @param sym
	 */
	private static void run_tests(PartitionModel model, int sym, int tries) {
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
		if (false) {
			solver.options().setSolver(SATFactory.MiniSat);
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				go_batch(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				psolver.setPs(1);
				solutions = psolver.solve(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				psolver.setPs(4);
				solutions = psolver.solve(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}	
		}
		
		// run under Glucose in batch, sequential and parallel mode
		if (true) {
			solver.options().setSolver(SATFactory.Glucose);
//			for (int i = 0; i < tries; i++) {
//				long t1 = System.currentTimeMillis();
//				go_incremental(b1, b2, f1, f2);
//				long t2 = System.currentTimeMillis();
//				System.out.print((t2-t1));
//				System.out.print("\t");
//			}
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				go_batch(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}
//			for (int i = 0; i < tries; i++) {
//				long t1 = System.currentTimeMillis();
//				psolver.setPs(1);
//				solutions = psolver.solve(b1, b2, f1, f2);
//				long t2 = System.currentTimeMillis();
//				System.out.print((t2-t1));
//				System.out.print("\t");
//			}
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				psolver.setPs(4);
				solutions = psolver.solve(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}	
		}
		
		// run under plingeling in batch
		if (false) {
			solver.options().setSolver(SATFactory.plingeling());
			for (int i = 0; i < tries; i++) {
				long t1 = System.currentTimeMillis();
				go_batch(b1, b2, f1, f2);
				long t2 = System.currentTimeMillis();
				System.out.print((t2-t1));
				System.out.print("\t");
			}
		}
		
		System.out.print(solutions.size());
		System.out.print("\t");
		System.out.print(getGenTime(psolver));
		System.out.print("\t");
	}

	private static long getGenTime(ParallelSolver psolver2) {
		long counter = 0;
		for (PProblem p : solutions)
			counter = counter + p.getConfigTime();
		return counter;
	}

	/**
	 * Solves the problem under standard Kodkod (i.e., batch mode).
	 * @param b1
	 * @param b2
	 * @param f1
	 * @param f2
	 */
	private static void go_batch(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		Solution sol = solver.solve(f1.and(f2), b3);
//		System.out.print(sol.outcome());
	}

	private static void go_incremental(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		IncrementalSolver isolver = IncrementalSolver.solver(solver.options());

		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		isolver.solve(f1,b3);
		b3.relations().clear();
		Solution sol = isolver.solve(f2,b3);

//		isolver.solve(f1,b1);
//		Solution sol = isolver.solve(f2,b2);
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
		int tries = 1;
		
//		System.out.print("FC10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,true,false,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("FL10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,true,true,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("FS10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,false,true,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("VC10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,true,false,true}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("VL10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,true,true,true}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("VS10\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,10,false,true,true}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("FC20\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,20,true,false,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("FL20\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,20,true,true,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
//
//		System.out.print("FS20\n");
//		for (int i = 5; i <= 5; i ++) {
//			System.out.print(i+"\t");
//			run_tests(new RingP(new Object[]{i,20,false,true,false}),20,tries);
//			System.out.print("\n");
//			stats.put(i, solutions);
//		}
//		System.out.print("\n");
////		printConfigs();
		
		System.out.print("VC20\n");
		for (int i = 5; i <= 5; i ++) {
			System.out.print(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,false,true}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs(); 
		
		System.out.print("VL20\n");
		for (int i = 5; i <= 5; i ++) {
			System.out.print(i+"\t");
			run_tests(new RingP(new Object[]{i,20,true,true,true}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

		System.out.print("VS20\n");
		for (int i = 5; i <= 10; i ++) {
			System.out.print(i+"\t");
			run_tests(new RingP(new Object[]{i,20,false,true,true}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
//		printConfigs();
	}

	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() {
		int tries = 2;

		System.out.print("NoIntervenes10\n"); 
		for (int i = 1; i <= 9; i ++) {
			System.out.print(i+"\t");
			run_tests(new HotelP(new Object[]{i,10,false}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

		System.out.print("Intervenes10\n"); 
		for (int i = 1; i <= 5; i ++) {
			System.out.print(i+"\t");
			run_tests(new HotelP(new Object[]{i,10,true}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();
		
		System.out.print("NoIntervenes20\n"); 
		for (int i = 1; i <= 6; i ++) {
			System.out.print(i+"\t");
			run_tests(new HotelP(new Object[]{i,20,false}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

		System.out.print("Intervenes20\n"); 
		for (int i = 1; i <= 5; i ++) {
			System.out.print(i+"\t");
			run_tests(new HotelP(new Object[]{i,20,true}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();
	}
	
	/**
	 * Tests the performance of all variants of the Handshake example.
	 */
	private static void runHandshake() {
		int tries = 1;
		
		System.out.print("FI\n"); 
		for (int i = 3; i <= 14; i ++) {
			System.out.print(i+"\t");
			run_tests(new HandshakeP(new Object[]{false,true,i}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();
		
		System.out.print("VI\n"); 
		for (int i = 3; i <= 14; i ++) {
			System.out.print(i+"\t");
			run_tests(new HandshakeP(new Object[]{true,true,i}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

		System.out.print("FT\n"); 
		for (int i = 3; i <= 14; i ++) {
			System.out.print(i+"\t");
			run_tests(new HandshakeP(new Object[]{false,false,i}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

		System.out.print("VT\n"); 
		for (int i = 3; i <= 14; i ++) {
			System.out.print(i+"\t");
			run_tests(new HandshakeP(new Object[]{true,false,i}),20,tries);
			System.out.print("\n");
			stats.put(i, solutions);
		}
		System.out.print("\n");
//		printConfigs();

	}


}