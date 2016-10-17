package kodkod.test.pardinus.decomp;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.text.Format;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kodkod.engine.DecomposedKodkodSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DProblem;
import kodkod.examples.pardinus.decomp.DiffEgP;
import kodkod.examples.pardinus.decomp.DijkstraP;
import kodkod.examples.pardinus.decomp.DiningP;
import kodkod.examples.pardinus.decomp.FilesystemP;
import kodkod.examples.pardinus.decomp.HandshakeP;
import kodkod.examples.pardinus.decomp.HotelP;
import kodkod.examples.pardinus.decomp.LiftP;
import kodkod.examples.pardinus.decomp.NetconfigP;
import kodkod.examples.pardinus.decomp.PeaceableP;
import kodkod.examples.pardinus.decomp.RedBlackTreeP;
import kodkod.examples.pardinus.decomp.RingP;
import kodkod.examples.pardinus.decomp.SpanP;

public final class RunTestsP {

	final static DecomposedKodkodSolver psolver = new DecomposedKodkodSolver();

	final static Map<Integer,List<DProblem>> stats = new HashMap<Integer,List<DProblem>> ();

	static DProblem psolution = null;
	static Solution solution = null;

	static int tries, threads = 4;

	static private StringBuilder log = new StringBuilder();
	static private StringBuilder header = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, file, handshake, span, dijkstra, diffeg, netconfig, redblack, dining, peaceable, jobs, lift, avl;

	private static List<DMode> modes = new ArrayList<DMode>();
	private static List<Solvers> solvers = new ArrayList<Solvers>();

	/**
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		tries = Integer.valueOf(args[0]);

		if(opts.contains("-ms")) solvers.add(Solvers.MINISAT);
		if(opts.contains("-gl")) solvers.add(Solvers.GLUCOSE);
		if(opts.contains("-sy")) solvers.add(Solvers.SYRUP);
		if(opts.contains("-pl")) solvers.add(Solvers.PLINGELING);

		if(opts.contains("-t")) modes.add(DMode.EXHAUSTIVE);
		if(opts.contains("-b")) modes.add(DMode.BATCH);
		if(opts.contains("-s")) { modes.add(DMode.PARALLEL); threads = 1;}
		if(opts.contains("-p")) modes.add(DMode.PARALLEL);
		if(opts.contains("-h")) modes.add(DMode.HYBRID);
		if(opts.contains("-i")) modes.add(DMode.INCREMENTAL);


		if (opts.contains("--all")) {
			diffeg = true;
			dijkstra = true;
			dining = true;
			file = true;
			handshake = true;
			hotel = true;
			jobs = true;
			lift = true;
			peaceable = true;
			redblack = true;
			avl = true;
			netconfig = true;
			ring = true;
			span = true;
		} else {
			diffeg = opts.contains("--diffeg");
			dijkstra = opts.contains("--dijkstra");
			dining = opts.contains("--dining");
			file = opts.contains("--file");
			handshake = opts.contains("--handshake");
			hotel = opts.contains("--hotel");
			jobs = opts.contains("--jobs");
			lift = opts.contains("--lift");
			peaceable = opts.contains("--peaceable");
			redblack = opts.contains("--redblack");
			avl = opts.contains("--avl");
			netconfig = opts.contains("--netconfig");
			ring = opts.contains("--ring");
			span = opts.contains("--span");
		}
		
		printHeader();
		flush();

		if (diffeg) runDiffEg();
		if (dijkstra) runDijkstra();
		if (dining) runDining();
		if (file) runFileSystem();
		if (handshake) runHandshake();
		if (hotel) runHotel();
        if (jobs) runJobs();
        if (lift) runLift();
        if (peaceable) runPeaceable();
        if (redblack) runRedBlack();
        if (avl) runAVL();
        if (netconfig) runNetconfig();
		if (ring) runRing();
		if (span) runSpanTree();

	}

	private static void runPeaceable() throws IOException, InterruptedException {
		String model = PeaceableP.class.getCanonicalName();
		log.append("Peaceable Queens\n"); 
		log.append(header);
		flush();
		for (int i = 6; i <= 10; i ++)  {
			for (int j = 6; j <= 10; j ++)  {
				log.append(i+" "+j+"\t"); flush();
				runModes(model, new String[]{i+"",j+""});
				log.append("\n"); flush();
			}		
		}
		log.append("\n");		
	}

	private static void runLift() throws IOException, InterruptedException {
		String model = LiftP.class.getCanonicalName();
		log.append("LiftSPL\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 8; i ++)  {
			for (int j = 8; j <= 20; j ++)  {
				log.append(i+" "+j+"\t"); flush();
				runModes(model, new String[]{i+"",j+""});
				log.append("\n"); flush();
			}		
		}
		log.append("\n");				
	}

	private static void runJobs() {
		// TODO Auto-generated method stub
		
	}

	private static void printHeader() {
		Format formatter = new SimpleDateFormat("YYYY-MM-dd_HH-mm-ss");
		log.append("\n------\n");
		log.append(formatter.format(new Date()));
		log.append("\n");
		log.append("Examples: ");
		if (hotel) log.append("Hotel ");
		if (ring) log.append("RingLeader ");
		if (handshake) log.append("Handshake ");
		if (file) log.append("FileSystem ");
		if (span) log.append("SpanTree ");
		if (redblack) log.append("RedBlackTree ");
		if (avl) log.append("AVLTree ");
		if (dijkstra) log.append("Dijkstra ");
		log.append("\n");

		log.append("Solvers: ");
		log.append(solvers);
		log.append("\n");

		log.append("Modes: ");
		log.append(modes);
		log.append("\n");

		log.append("Tries: ");
		log.append(tries);
		log.append("\n");

		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

		header.append("n\t");
		if (solvers.contains(Solvers.MINISAT)) {
			if (modes.contains(DMode.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("M.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("M.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("M.H\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("M.I\tSat\t");
		}

		if (solvers.contains(Solvers.GLUCOSE)) {
			if (modes.contains(DMode.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("G.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("G.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("G.H\tSat\tC.#\tC.t\t");
			if (modes.contains(kodkod.engine.config.DecomposedOptions.DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("G.I\tSat\t");
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (modes.contains(DMode.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("S.B\tSat\t");
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (modes.contains(DMode.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("P.B\tSat\t");
		}

		header.append("\n");
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	/**
	 * Runs a model instance instance for the specified number of times.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static int runModelInstance(String model, String[] model_args, int tries) throws IOException, InterruptedException {
		String javaHome = System.getProperty("java.home");
		String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
		String classpath = System.getProperty("java.class.path");
		String className = RunTestModel.class.getCanonicalName();
		String librarypath = System.getProperty("java.library.path");

		String[] cmd_args = new String[]{javaBin, "-Djava.library.path="+librarypath, "-cp", classpath, className, model};

		String[] args = Arrays.copyOf(cmd_args, cmd_args.length + model_args.length);
		System.arraycopy(model_args, 0, args, cmd_args.length, model_args.length);

		int exitVal = -1;

		for (int k = 0; k < tries; k++) {
			Process p = Runtime.getRuntime().exec(args);

			InputStream stderr = p.getErrorStream();
			InputStreamReader isr = new InputStreamReader(stderr);
			BufferedReader br = new BufferedReader(isr);
			String line = null;
			while ( (line = br.readLine()) != null)
				System.out.println(line);
			exitVal = p.waitFor();
			System.out.print("OK\t\t");
		}

		return exitVal;
	}

	/**
	 * Runs a model variant for the specified modes and solvers.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModes(String model, String[] model_args) throws IOException, InterruptedException {
		String[] args = new String[model_args.length+3];
		System.arraycopy(model_args, 0, args, 3, model_args.length);
		args[2] = threads+"";

		if (modes.contains(DMode.EXHAUSTIVE)) {
			args[0] = DMode.EXHAUSTIVE.name();
			args[1] = Solvers.GLUCOSE.name();
			args[2] = "1";
			runModelInstance(model,args,1);
			return ;
		}
		
		if (solvers.contains(Solvers.MINISAT)) {
			args[1] = Solvers.MINISAT.name();
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.GLUCOSE)) {
			args[1] = Solvers.GLUCOSE.name();
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (modes.contains(DMode.BATCH)) {
				args[0] = DMode.BATCH.name();
				args[1] = Solvers.SYRUP.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (modes.contains(DMode.BATCH)) {
				args[0] = DMode.BATCH.name();
				args[1] = Solvers.PLINGELING.name();
				runModelInstance(model,args,tries);
			}
		}

	}

	/**
	 * Tests the performance of all variants of the Ring example.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runRing() throws IOException, InterruptedException {
		String model = RingP.class.getCanonicalName();

//		int t = 10;
//
//		for (RingP.Variant2 s : RingP.Variant2.values())
//			for (RingP.Variant1 v : RingP.Variant1.values()) {
//				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
//				log.append(header);
//				flush();
//				for (int i = 1; i <= 8; i ++)  {
//					log.append(i+"\t"); flush();
//					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
//					log.append("\n"); flush();
//				}
//				log.append("\n");
//			}

		int t = 20;

		RingP.Variant2 s = RingP.Variant2.VARIABLE;
//		for (RingP.Variant2 s : RingP.Variant2.values())
//			for (RingP.Variant1 v : RingP.Variant1.values()) {
				RingP.Variant1 v = RingP.Variant1.BADLIVENESS;
				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 13; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
				
				v = RingP.Variant1.GOODLIVENESS;
				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 6; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
				
				v = RingP.Variant1.GOODSAFETY;
				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 8; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
//			}

	}

	/**
	 * Tests the performance of all variants of the Handshake example.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runHandshake() throws IOException, InterruptedException {
		String model = HandshakeP.class.getCanonicalName();

		HandshakeP.Variant2 s = HandshakeP.Variant2.STATIC;
//		for (HandshakeP.Variant2 s : HandshakeP.Variant2.values())
//			for (HandshakeP.Variant1 v : HandshakeP.Variant1.values()) {
				HandshakeP.Variant1 v = HandshakeP.Variant1.COUNTER;
				log.append(v.name()+" "+s.name()+"\n"); 
				log.append(header);
				flush();
				for (int i = 3; i <= 20; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
				
				v = HandshakeP.Variant1.THEOREM;
				log.append(v.name()+" "+s.name()+"\n"); 
				log.append(header);
				flush();
				for (int i = 3; i <= 15; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
//			}
	}

	private static void runRedBlack() throws IOException, InterruptedException {

		String model = RedBlackTreeP.class.getCanonicalName();

		RedBlackTreeP.Variant2 s = RedBlackTreeP.Variant2.V1;
//		for (RedBlackTreeP.Variant1 v : RedBlackTreeP.Variant1.values()) {
		RedBlackTreeP.Variant1 v = RedBlackTreeP.Variant1.COUNTER;
			log.append("Red Black Tree "+v.name()+" "+s.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name(), s.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
			
			v = RedBlackTreeP.Variant1.THEOREM;
			log.append("Red Black Tree "+v.name()+" "+s.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 12; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name(), s.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
//		}
	}
	

	private static void runAVL() throws IOException, InterruptedException {

	}

	private static void runSpanTree() throws IOException, InterruptedException {

		String model = SpanP.class.getCanonicalName();
		int t = 9;
//		for (SpanP.Variant v : SpanP.Variant.values()) {
			SpanP.Variant v = SpanP.Variant.V1;
			log.append("Span"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 18; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
			
			v = SpanP.Variant.V2;
			log.append("Span"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 18; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
//		}

//		t = 12;
//		for (SpanP.Variant v : SpanP.Variant.values()) {
//			log.append("Span"+t+" "+v.name()+"\n"); 
//			log.append(header);
//			flush();
//			for (int i = 2; i <= 20; i ++)  {
//				log.append(i+"\t"); flush();
//				runModes(model, new String[]{i+"", t+"",v.name()});
//				log.append("\n"); flush();
//			}
//			log.append("\n");
//		}
	}

	private static void runDijkstra() throws IOException, InterruptedException {

		String model = DijkstraP.class.getCanonicalName();
		int t = 15;
		for (DijkstraP.Variant v : DijkstraP.Variant.values()) {
			log.append("Dijkstra"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 30; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}
	
	private static void runDining() throws IOException, InterruptedException {
		String model = DiningP.class.getCanonicalName();
		log.append("Dining"+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 20; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");		
	}


	private static void runDiffEg() throws IOException, InterruptedException {

		String model = DiffEgP.class.getCanonicalName();
		log.append("DiffEg"+"\n"); 
		log.append(header);
		flush();
		for (int i = 30; i <= 40; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}

	private static void runNetconfig() throws IOException, InterruptedException {

		String model = NetconfigP.class.getCanonicalName();
		log.append("Netconfig"+"\n"); 
		log.append(header);
		flush();
		for (int i = 3; i <= 20; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",1+"",i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}


	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() throws IOException, InterruptedException {
		String model = HotelP.class.getCanonicalName();

//		int t = 10;
//
//		for (HotelP.Variant v : HotelP.Variant.values()) {
//			log.append(v.name()+" "+t+"\n"); 
//			log.append(header);
//			flush();
//			for (int i = 1; i <= 6; i ++)  {
//				log.append(i+"\t"); flush();
//				runModes(model, new String[]{i+"", t+"", v.name()});
//				log.append("\n"); flush();
//			}
//			log.append("\n");
//		}

		int t = 20;

//		for (HotelP.Variant v : HotelP.Variant.values()) {
			HotelP.Variant v = HotelP.Variant.INTERVENES;
			log.append(v.name()+" "+t+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
//		}
			v = HotelP.Variant.NOINTERVENES;
			log.append(v.name()+" "+t+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 6; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
	}


	private static void runFileSystem() throws IOException, InterruptedException {
		String model = FilesystemP.class.getCanonicalName();

		for (FilesystemP.Variant v : FilesystemP.Variant.values()) {
			log.append(v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 3; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}
	
	
	public enum Solvers {
		GLUCOSE,
		MINISAT,
		SYRUP,
		PLINGELING;
	}
	

}