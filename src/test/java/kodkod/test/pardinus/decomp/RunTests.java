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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import kodkod.engine.ExtendedSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DProblem;
import kodkod.examples.pardinus.temporal.DijkstraT;
import kodkod.examples.pardinus.temporal.RingT;
import kodkod.examples.pardinus.temporal.SpanT;
import kodkod.examples.pardinus.temporal.HotelT;

public final class RunTests {

	final static Map<Integer,List<DProblem<ExtendedSolver>>> stats = new HashMap<Integer,List<DProblem<ExtendedSolver>>> ();

	static DProblem<ExtendedSolver> psolution = null;
	static Solution solution = null;

	static int tries, threads = 4, max_trace;
	static String timeout = "10m";

	static private boolean batch = false;
	
	static private boolean reif = false, satit = false;
	
	static private StringBuilder log = new StringBuilder();
	static private StringBuilder header = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, span, dijkstra;

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
		max_trace = Integer.valueOf(args[1]);

		if(opts.contains("-ms")) solvers.add(Solvers.MINISAT);
		if(opts.contains("-gl")) solvers.add(Solvers.GLUCOSE);
		if(opts.contains("-sy")) solvers.add(Solvers.SYRUP);
		if(opts.contains("-pl")) solvers.add(Solvers.PLINGELING);
		if(opts.contains("-xb")) solvers.add(Solvers.NUXMVB);
		if(opts.contains("-xc")) solvers.add(Solvers.NUXMVC);
		if(opts.contains("-sb")) solvers.add(Solvers.NUSMVB);
		if(opts.contains("-sc")) solvers.add(Solvers.NUSMVC);
		
		if(opts.contains("-t")) modes.add(DMode.EXHAUSTIVE);
		if(opts.contains("-b")) batch = true;
		if(opts.contains("-s")) { modes.add(DMode.PARALLEL); threads = 1;}
		if(opts.contains("-p")) modes.add(DMode.PARALLEL);
		if(opts.contains("-h")) modes.add(DMode.HYBRID);
		if(opts.contains("-i")) modes.add(DMode.INCREMENTAL);

		if(opts.contains("-satit")) satit = true;
		if(opts.contains("-reif")) reif = true;

		if (opts.contains("--all")) {
			dijkstra = true;
			hotel = true;
			ring = true;
			span = true;
		} else {
			dijkstra = opts.contains("--dijkstra");
			hotel = opts.contains("--hotel");
			ring = opts.contains("--ring");
			span = opts.contains("--span");
		}
		
		printHeader();
		flush();

		if (dijkstra) runDijkstra();
		if (hotel) runHotel();
		if (ring) runRing();
		if (span) runSpanTree();

	}

	private static void printHeader() {
		Format formatter = new SimpleDateFormat("YYYY-MM-dd_HH-mm-ss");
		log.append("\n------\n");
		log.append(formatter.format(new Date()));
		log.append("\n");
		log.append("Examples: ");
		if (hotel) log.append("Hotel ");
		if (ring) log.append("RingLeader ");
		if (span) log.append("SpanTree ");
		if (dijkstra) log.append("Dijkstra ");
		log.append("\n");

		log.append("Solvers: ");
		log.append(solvers);
		log.append("\n");

		log.append("Modes: ");
		List<String> aux = modes.stream().map(x->x.toString()).collect(Collectors.toList());
		if (batch) aux.add("BATCH");
		log.append(aux);
		log.append("\n");

		log.append("Max trace: ");
		log.append(max_trace);
		log.append("\n");

		log.append("Tries: ");
		log.append(tries);
		log.append("\n");

		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

		header.append("n\t");
		if (solvers.contains(Solvers.MINISAT)) {
			if (batch)
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
			if (batch)
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
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("S.B\tSat\t");
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("P.B\tSat\t");
		}
		

		if (solvers.contains(Solvers.NUXMVB)) {
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("XB.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("XB.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("XB.H\tSat\tC.#\tC.t\t");
			if (modes.contains(kodkod.engine.config.DecomposedOptions.DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("XB.I\tSat\t");
		}
		
		if (solvers.contains(Solvers.NUSMVB)) {
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("SB.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("SB.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("SB.H\tSat\tC.#\tC.t\t");
			if (modes.contains(kodkod.engine.config.DecomposedOptions.DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("SB.I\tSat\t");
		}
		
		if (solvers.contains(Solvers.NUXMVC)) {
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("XC.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("XC.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("XC.H\tSat\tC.#\tC.t\t");
			if (modes.contains(kodkod.engine.config.DecomposedOptions.DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("XC.I\tSat\t");
		}
		
		if (solvers.contains(Solvers.NUSMVC)) {
			if (batch)
				for (int i = 0; i < tries; i++)
					header.append("SC.B\tSat\t");
			if (modes.contains(DMode.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("SC.P\tSat\tC.#\tC.t\t");
			if (modes.contains(DMode.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("SC.H\tSat\tC.#\tC.t\t");
			if (modes.contains(kodkod.engine.config.DecomposedOptions.DMode.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("SC.I\tSat\t");
		}
		

		header.append("\n");
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}
	
	static Set<List<String>> cached_timeouts = new HashSet<List<String>>();

	/**
	 * Runs a model instance instance for the specified number of times.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static int runModelInstance(String model, String[] model_args, int tries) throws IOException, InterruptedException {
		String javaHome = System.getProperty("java.home");
		String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
		String classpath = System.getProperty("java.class.path");
		String className = kodkod.test.pardinus.temporal.RunSolveModel.class.getCanonicalName();
		String librarypath = System.getProperty("java.library.path");

		String[] cmd_args = new String[]{"gtimeout", timeout, javaBin, "-Djava.library.path="+librarypath,"-cp", classpath, className, model};

		String[] args = Arrays.copyOf(cmd_args, cmd_args.length + model_args.length);
		System.arraycopy(model_args, 0, args, cmd_args.length, model_args.length);

		int exitVal = -1;
		
		List<String> cache = new ArrayList<String>(Arrays.asList(model_args));
		cache.remove(6);
		
		for (int k = 0; k < tries; k++) {
			if (cached_timeouts.contains(cache)) {
				log.append("TO\t\t");
				if (!cache.contains("BATCH")) {
					log.append("\t\t");
				}
			} else {
				Process p = Runtime.getRuntime().exec(args);
	
				InputStream stderr = p.getErrorStream();
				InputStreamReader isr = new InputStreamReader(stderr);
				BufferedReader br = new BufferedReader(isr);
				String line = null;
				while ( (line = br.readLine()) != null)
					System.out.println(line);
				exitVal = p.waitFor();
				if (exitVal == 0) {
					System.out.print("OK\t\t");
					if (!cache.contains("BATCH")) {
						System.out.print("\t\t");
					}
				}
				else {
	//				System.out.print("TO\t\t");
					log.append("TO\t\t");
					if (!cache.contains("BATCH")) {
						log.append("\t\t");
					}
					cached_timeouts.add(cache);
				}
			}
			flush();
		}

		return exitVal;
	}

	/**
	 * Runs a model variant for the specified modes and solvers.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModes(String model, String[] model_args) throws IOException, InterruptedException {
		String[] args = new String[model_args.length+6];
		System.arraycopy(model_args, 0, args, 6, model_args.length);
		args[2] = max_trace+"";
		args[3] = threads+"";
		args[4] = satit+"";
		args[5] = reif+"";

		if (modes.contains(DMode.EXHAUSTIVE)) {
			args[0] = DMode.EXHAUSTIVE.name();
			args[1] = Solvers.GLUCOSE.name();
			args[3] = "1";
			runModelInstance(model,args,1);
			return ;
		}
		
		if (solvers.contains(Solvers.MINISAT)) {
			args[1] = Solvers.MINISAT.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.GLUCOSE)) {
			args[1] = Solvers.GLUCOSE.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (batch) {
				args[0] = "BATCH";
				args[1] = Solvers.SYRUP.name();
				runModelInstance(model,args,tries);
			}
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (batch) {
				args[0] = "BATCH";
				args[1] = Solvers.PLINGELING.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUXMVB)) {
			args[1] = Solvers.NUXMVB.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUSMVB)) {
			args[1] = Solvers.NUSMVB.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUXMVC)) {
			args[1] = Solvers.NUXMVC.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
				runModelInstance(model,args,tries);
			}
		}
		
		if (solvers.contains(Solvers.NUSMVC)) {
			args[1] = Solvers.NUSMVC.name();
			if (batch) {
				args[0] = "BATCH";
				runModelInstance(model,args,tries);
			}
			for (DMode m : modes) {
				args[0] = m.name();
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
		String model = RingT.class.getCanonicalName();

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

//		int t = 20;

		RingT.Variant2 s = RingT.Variant2.VARIABLE;
//		for (RingP.Variant2 s : RingP.Variant2.values())
//			for (RingP.Variant1 v : RingP.Variant1.values()) {
				RingT.Variant1 v = RingT.Variant1.BADLIVENESS;
//				log.append(v.name()+" "+s.name()+"\n"); 
//				log.append(header);
//				flush();
//				for (int i = 1; i <= 12; i ++)  {
//					log.append(i+"\t"); flush();
//					runModes(model, new String[]{i+"", v.name(), s.name()});
//					log.append("\n"); flush();
//				}
//				log.append("\n");
//				
//				v = RingT.Variant1.GOODLIVENESS;
//				log.append(v.name()+" "+s.name()+"\n"); 
//				log.append(header);
//				flush();
//				for (int i = 1; i <= 4; i ++)  {
//					log.append(i+"\t"); flush();
//					runModes(model, new String[]{i+"", v.name(), s.name()});
//					log.append("\n"); flush();
//				}
//				log.append("\n");
				
				v = RingT.Variant1.GOODSAFETY;
				log.append(v.name()+" "+s.name()+"\n"); 
				log.append(header);
				flush();
				for (int i = 5; i <= 8; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
//			}

	}

	private static void runSpanTree() throws IOException, InterruptedException {

		String model = SpanT.class.getCanonicalName();
//		int t = 9;
//		for (SpanP.Variant v : SpanP.Variant.values()) {
			SpanT.Variant v = SpanT.Variant.V1;
			log.append("Span "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 16; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
			
			v = SpanT.Variant.V2;
			log.append("Span "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 16; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"",v.name()});
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

		String model = DijkstraT.class.getCanonicalName();
//		int t = 15;
		for (DijkstraT.Variant v : DijkstraT.Variant.values()) {
			log.append("Dijkstra "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 15; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}
	
	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() throws IOException, InterruptedException {
		String model = HotelT.class.getCanonicalName();

//		int t = 10;
//
//		for (HotelT.Variant v : HotelT.Variant.values()) {
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

//		for (HotelT.Variant v : HotelT.Variant.values()) {
			HotelT.Variant v = HotelT.Variant.INTERVENES;
			log.append(v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 5; i <= 10 ; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
//		}
			v = HotelT.Variant.NOINTERVENES;
			log.append(v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 4; i <= 4; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
	}

	public enum Solvers {
		GLUCOSE,
		MINISAT,
		SYRUP,
		PLINGELING,
		NUSMVC,
		NUXMVC,
		NUSMVB,
		NUXMVB,
	}
	

}