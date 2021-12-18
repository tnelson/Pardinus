package kodkod.engine.proofExplanation.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.util.ints.IntBitSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

/**
 * An implementation of the {@linkplain ResolutionTrace} interface inspired by
 * Emina Torlak's {@linkplain LazyTrace} implementation. Acts as a proxy for the interface
 * reducing a {@linkplain ResolutionTrace} according to a set of assumption literals.
 * In particular, the assumption literals are unit-propagated on the axioms of the original
 * trace, and new resolvents are built up from that point on.
 */
public class ReducedResolutionTrace implements ResolutionTrace {

    // ensure that you can either add or remove antecedents from ClauseView (currently going with add)
    // so that we can build the tree structure of the trace as we move down.

    private ResolutionTrace origTrace;
    private Map<Integer, ClauseView> reducedClauseMap;
    private Clause[] reducedTrace;
    private final ClauseView EMPTY_CLAUSE = new ClauseView(new ArrayList<>(), new ArrayList<>());

    // [[ ]] thought: what if we only used Iterator<Clause>s instead of lists of Clauses?

    // traverses the trace breadth-first, starting from the empty clause, running our
    // reduced trace construction algorithm.
    public ReducedResolutionTrace(ResolutionTrace origTrace, IntSet assumps) {
        this.origTrace = origTrace;
        this.reducedClauseMap = new HashMap<>();
        Map<Integer, ClauseView> reducedTraceMap = new HashMap<>();        
        Queue<Pair<Clause, Optional<Integer>>> bfsQueue = new LinkedList<>();
        Set<Clause> visited = new HashSet<>();

        Iterator<Clause> reverseOrigClauseIterator = origTrace.reverseIterator();
        if (reverseOrigClauseIterator.hasNext()) {
            Pair<Clause, Optional<Integer>> root = new Pair<>(reverseOrigClauseIterator.next(), Optional.empty());
            System.out.println("Root antecedents: " + constructAntecedentsList(root.getKey()));
            try {
                Map<Integer, ClauseView> reducedTree = reductionProcess(root, bfsQueue, visited, reducedTraceMap, assumps);
                this.reducedClauseMap = reducedTree;
            } catch (Exception e) {
                System.err.println(e.getMessage());
            }
        }

        Iterator<Clause> origClauseIterator = origTrace.iterator();
        this.reducedTrace = new Clause[reducedClauseMap.size() + 1];
        int i = 0;
        while (origClauseIterator.hasNext()) {
            Clause origClause = origClauseIterator.next();
            if (reducedClauseMap.containsKey(origClause.hashCode())) {
                this.reducedTrace[i] = reducedClauseMap.get(origClause.hashCode());
                i++;
            }
        }

        System.out.println("Printing out reducedClauseMap values: "); // debugging
        for (Clause c : reducedClauseMap.values()) {
            System.out.println(c);
            System.out.println("  antes=");
            Iterator<Clause> it2 = c.antecedents();
            while(it2.hasNext()) {
                System.out.println("    " + it2.next());
            }
        }
        System.out.println("~~~~~~");
    }

    // ADD STUFF THAT DOESN'T HAVE ANTECEDENTS TO THE TREE
    // BUT STUFF IN THE QUEUE SHOULD HAVE ANTECEDENTS

    // TODO: document
    private Map<Integer, ClauseView> reductionProcess (
        Pair<Clause, Optional<Integer>> currPair, 
        Queue<Pair<Clause, Optional<Integer>>> bfsQueue, Set<Clause> visited, 
        Map<Integer, ClauseView> reducedTraceMap, IntSet assumps) throws Exception {

        Clause currClause = currPair.getKey();
        Optional<Integer> parentHashOpt = currPair.getValue();
        List<Integer> currLiterals = constructLiteralsList(currClause);
        boolean containsAssump = false;
        ClauseView newParent = new ClauseView(currClause);
        System.out.println("Current pair: " + currPair);
        System.out.println("Current clause, expanded: ");
        System.out.println(currClause);
        System.out.println("  antes=");
        Iterator<Clause> it0 = currClause.antecedents();
        while(it0.hasNext()) {
            System.out.println("    " + it0.next());
        }
        System.out.println("New bfsQueue: " + bfsQueue);
        System.out.println("Current tree: "); // debugging
        for (Clause c : reducedTraceMap.values()) {
            System.out.println(c);
            System.out.println("  antes=");
            Iterator<Clause> it2 = c.antecedents();
            while(it2.hasNext()) {
                System.out.println("    " + it2.next());
            }
        }
        System.out.println(" - - - - - - - ");

        // C == {} case:
        //    if C is an empty clause {}, push antecedents to queue. if no antecedents, move onto the queue.
        if (currLiterals.isEmpty()) {
            Iterator<Clause> anteIterator = currClause.antecedents();
            ClauseView currClauseView = new ClauseView(new ArrayList<>(), constructLiteralsList(currClause));
            int currHashCode = currClause.hashCode();
            reducedTraceMap.put(currHashCode, currClauseView);
            while (anteIterator.hasNext()) {
                Clause ante = anteIterator.next();
                // debug NOTE: ante is correct at this point for `ante`
                ClauseView anteClauseView = new ClauseView(ante);
                // debug NOTE: anteClauseView has INCORRECT antes. need to fix ClauseView constructor.
                // TODO: fix identified bug in `constructAntecedentsList`
                Pair<Clause, Optional<Integer>> newPair = new Pair<>(anteClauseView, Optional.of(currHashCode));
                bfsQueue.add(newPair);
            }
            if (bfsQueue.isEmpty()) {
                return reducedTraceMap;
            } else {
                Pair<Clause, Optional<Integer>> firstPair = bfsQueue.poll();
                return reductionProcess(firstPair, bfsQueue, visited, reducedTraceMap, assumps);
            }
        } else {
            IntIterator assumpIterator = assumps.iterator();
            while (assumpIterator.hasNext()) {
                int assump = assumpIterator.next();

                // C contains A case:
                //    if C contains A for any assump A, we simply ignore it and move on
                if (currLiterals.contains(assump)) {
                    containsAssump = true;
                    break;
                    // transition: move on to next item of queue
                }

                // C == -A case:
                //    if C is -A for any assump A, throw away tree so far, throw away queue, and restart at empty clause
                //    and push on antecedents of C
                if ((currLiterals.size() == 1) && (currLiterals.get(0) == (-1 * assump))) {
                    Iterator<Clause> anteIterator = currClause.antecedents();
                    Queue<Pair<Clause, Optional<Integer>>> newBfsQueue = new LinkedList<>();
                    while (anteIterator.hasNext()) {
                        Pair<Clause, Optional<Integer>> newPair = new Pair<>(anteIterator.next(), Optional.of(currClause.hashCode()));
                        newBfsQueue.add(newPair);
                    }
                    Map<Integer, ClauseView> newReducedTraceMap = new HashMap<>();
                    newReducedTraceMap.put(0, EMPTY_CLAUSE);
                    return reductionProcess(new Pair(EMPTY_CLAUSE, Optional.empty()), newBfsQueue, visited, newReducedTraceMap, assumps);
                }

                // TODO: add visited check

                // C is other clause case:
                //     if C is any other clause and unitProp(C, A) is parent, remove other children from queue
                //     else, add unitProp(C, A) to the tree, and push antecedents of C to the queue
                Optional<Clause> unitProppedClauseOpt = unitPropagateAllOpt(currClause, assumps);
                // given our prior checks, this should always be true
                if (unitProppedClauseOpt.isPresent()) {
                    Clause unitProppedClause = unitProppedClauseOpt.get();
                    List<Integer> unitProppedLiterals = constructLiteralsList(unitProppedClause);
                    // check literals equality with parent
                    if (parentHashOpt.isPresent() && (reducedTraceMap.containsKey(parentHashOpt.get()))) {
                        Integer parentHash = parentHashOpt.get();
                        Clause parentClause = reducedTraceMap.get(parentHash);
                        List<Integer> parentLiterals = constructLiteralsList(parentClause);
                        if (unitProppedLiterals.equals(parentLiterals)) {
                            // add to tree. remove elements of queue with same parent.
                            boolean queueContainsSiblings = true;
                            while (queueContainsSiblings) {
                                Optional<Integer> nextParent = bfsQueue.peek().getValue();
                                if (nextParent.isPresent() && nextParent.get().equals(parentHash)) {
                                    bfsQueue.poll();
                                } else {
                                    queueContainsSiblings = false;
                                }
                            }
                        }
                    }
                    newParent = new ClauseView(unitProppedClause);
                    // TODO: fix
                    if (!visited.contains(unitProppedClause)) {
                        reducedTraceMap.put(currClause.hashCode(), newParent);
                    }
                    Iterator<Clause> anteIterator = currClause.antecedents();
                    while (anteIterator.hasNext()) {
                        // TODO: if we're dealing with hashCodes, what should currClause be replaced with, if anything?
                        Pair<Clause, Optional<Integer>> newPair = new Pair<>(anteIterator.next(), Optional.of(currClause.hashCode()));
                        bfsQueue.add(newPair);
                    }
                }
            }

        }

        if (parentHashOpt.isPresent() && !containsAssump) {
            int parentHash = parentHashOpt.get();
            if (reducedTraceMap.containsKey(parentHash)) {
                ClauseView parentClauseView = reducedTraceMap.get(parentHash);
                parentClauseView.addAntecedent(newParent);
            } else {
                throw new Exception("Assigned parent not found!");
            }
        }

        // if bfsQueue is not empty, move on to the next entry
        if (!bfsQueue.isEmpty()) {
            Pair<Clause, Optional<Integer>> nextPair = bfsQueue.poll();
            if (!currLiterals.isEmpty()) {
                visited.add(currClause);
            }
            return reductionProcess(nextPair, bfsQueue, visited, reducedTraceMap, assumps);
        } else {
            // if the bfsQueue is empty, then return the current tree
            return reducedTraceMap;
        }        
    }

    /**
     * Propagates a set of literals on a {@linkplain Clause} and returns an {@linkplain Optional} 
     * of a {@linkplain Clause} with the adjusted set of literals. The {@linkplain Optional} is 
     * empty when the clause reduces to true upon propagation. Assumes that the same propagation
     * has already been done on the antecedents.
     * @param clause The clause on which propagation is to be done.
     * @param assumps An IntSet referring to the indices of the literals that are to be propagated.
     */
    private Optional<Clause> unitPropagateAllOpt(Clause clause, IntSet assumps) {
        IntIterator assumpsIterator = assumps.iterator();
        Optional<Clause> updatedClauseOpt = Optional.of(clause);
        while (assumpsIterator.hasNext()) {
            int assump = assumpsIterator.next();
            updatedClauseOpt = unitPropagateOpt(updatedClauseOpt.get(), assump);
            if (!updatedClauseOpt.isPresent()) {
                return Optional.empty();
            }
        }
        return updatedClauseOpt;
    }

    /**
     * Propagates a literal on a {@linkplain Clause} and returns an {@linkplain Optional} 
     * of a {@linkplain Clause} with the adjusted set of literals. The {@linkplain Optional} is 
     * empty when the clause reduces to true upon propagation. Assumes that the same propagation
     * has already been done on the antecedents.
     * @param clause The clause on which propagation is to be done.
     * @param assump An integer referring to the index of the literal that is to be propagated.
     */
    public Optional<Clause> unitPropagateOpt(Clause clause, int assump) {
        IntIterator literalIterator = clause.literals();
        List<Integer> newLiterals = new ArrayList<Integer>();
        while (literalIterator.hasNext()) {
            int nextLiteral = literalIterator.next();
            if (assump == nextLiteral) {
                return Optional.empty();
            }
            if (assump != -1 * nextLiteral) {
                newLiterals.add(nextLiteral);
            }
        }
        List<Clause> antecedents = this.constructAntecedentsList(clause);

        // TODO: ASSUMES that antecedents have already been propagated on
        //  - assert statement?
        return Optional.of(new ClauseView(antecedents, newLiterals));
    }

    // TODO: document + re-evaluate need for this function
    private List<Clause> constructAntecedentsList(Clause clause) {
        Iterator<Clause> antecedentsIt = clause.antecedents();
        List<Clause> antecedents = new ArrayList<>();
        while (antecedentsIt.hasNext()) {
            // bug here: the .next() pointer is being added to the list multiple times,
            // so each elem of the antecedents list refers to the same thing.
            Clause nextAnte = antecedentsIt.next();
            System.out.println(clause.hashCode() + " : adding anteante: " + nextAnte);
            antecedents.add(nextAnte);
            System.out.println(clause.hashCode() + " : current antecedents: " + antecedents);
        }
        System.out.println(clause.hashCode() + " : antecedents (in constructor): " + antecedents);
        return antecedents;
    }

    // TODO: document + re-evaluate need for this function
    private List<Integer> constructLiteralsList(Clause clause) {
        IntIterator litIt = clause.literals();
        List<Integer> lits = new ArrayList<>();
        while (litIt.hasNext()) {
            lits.add(litIt.next());
        }
        return lits;
    }
    

    @Override
    public int size() {
        return reducedTrace.length;
    }

    @Override
    public Iterator<Clause> iterator() {
        List<Clause> trace = Arrays.asList(reducedTrace);
        return trace.iterator();
        /*
        return new ClauseIterator(new IntIterator() {
			int index = 0;
			public boolean hasNext() { return index>=0 && index < reducedTrace.length; }
			public int next() { 
				if (!hasNext()) throw new NoSuchElementException();
				return index++;
			}
			public void remove() { throw new UnsupportedOperationException(); } 
		});*/
    }

    /**
	 * Returns true if indices.min() >= 0 && indices.max() < this.size()
	 * @requires !indices.isEmpty()
	 * @return indices.min() >= 0 && indices.max() < this.size()
	 */
	private boolean valid(IntSet indices) {
		return indices.min() >= 0 && indices.max() < reducedTrace.length;
	}

    @Override
    public Iterator<Clause> iterator(IntSet indices) {
        if (indices.isEmpty() || valid(indices)) {
			return new ClauseIterator(indices.iterator());
		}
		throw new IndexOutOfBoundsException("invalid indices: " + indices);
    }

    @Override
    public Iterator<Clause> reverseIterator(IntSet indices) {
        if (indices.isEmpty() || valid(indices)) {
			return new ClauseIterator(indices.iterator(Integer.MAX_VALUE, Integer.MIN_VALUE));
		}
		throw new IndexOutOfBoundsException("invalid indices: " + indices);
    }

    /**
     * Keeps only those indices from a list of indices that correspond to clauses
     * in the reduced trace.
     * @param origIndices The original {@linkplain IntSet} of indices.
     * @return A IntSet representing the updated indices.
     */
    private IntSet getUpdatedIndices(IntSet origIndices) {
        IntBitSet updatedIndices = new IntBitSet(origIndices.size());
        IntIterator origIndicesIt = origIndices.iterator();
        while (origIndicesIt.hasNext()) {
            int origIndex = origIndicesIt.next();
            Clause origClause = origTrace.get(origIndex);
            if (reducedClauseMap.containsKey(origClause)) {
                updatedIndices.add(origIndex);
            }
        }
        return updatedIndices;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#reverseIterator()
	 */
	public Iterator<Clause> reverseIterator() { 
		return new ClauseIterator(new IntIterator() {
			int index = reducedTrace.length - 1;
			public boolean hasNext() { return index>=0 && index < reducedTrace.length; }
			public int next() { 
				if (!hasNext()) throw new NoSuchElementException();
				return index--;
			}
			public void remove() { throw new UnsupportedOperationException(); } 
		}); 
	}

    @Override
    public Clause get(int index) {
        Clause currClause = origTrace.get(index);
        // fix
        return reducedClauseMap.get(currClause.hashCode());
    }

    @Override
    public IntSet core() {
        IntSet origCore = origTrace.core();
        return getUpdatedIndices(origCore);
    }

    @Override
    public IntSet axioms() {
        IntSet origAxioms = origTrace.axioms();
        return getUpdatedIndices(origAxioms);
    }

    @Override
    public IntSet resolvents() {
        IntSet origResolvents = origTrace.resolvents();
        return getUpdatedIndices(origResolvents);
    }

    @Override
    public IntSet reachable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    @Override
    public IntSet backwardReachable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    @Override
    public IntSet learnable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    @Override
    public IntSet directlyLearnable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }
    
    /**
     * A mutable implementation of the Clause abstract class.
     * @author Swetabh Changkakoti
     */
    private class ClauseView extends Clause {

        private List<Clause> antecedents;
        private List<Integer> literals;

        protected ClauseView() {}

        // TODO: document
        ClauseView(List<Clause> antecedents, List<Integer> literals) {
            this.antecedents = antecedents;
            this.literals = literals;
        }

        ClauseView(Clause clause) {
            // TODO: do we need defensive copies here?
            this.antecedents = new ArrayList<>(constructAntecedentsList(clause));
            this.literals = new ArrayList<>(constructLiteralsList(clause));
        }

        // TODO: change this so that it doesn't set the current index to that of 
        //  - a clause that was erased in reduction
        /**
		 * Sets the state of this clause view to represent
		 * the ith clause in the trace and returns this.
		 * @ensures sets the state of this clause view to represent
		 * the ith clause in the trace
         * @throws Exception when trying to access an index that has been removed in reduction.
		 * @return this
		 */
		ClauseView set(int index) throws Exception {
            Clause origIthClause = origTrace.get(index);
            // building set of literals
            /*
            IntIterator litIterator = origIthClause.literals();
            Set<Integer> litSet = new HashSet<Integer>();
            while (litIterator.hasNext()) {
                litSet.add(litIterator.next());
            }
            */
            //Clause currIthClauseOrNull = reducedClauseMap.get(litSet.hashCode());
            Clause currIthClauseOrNull = reducedClauseMap.get(origIthClause.hashCode());
            if (currIthClauseOrNull == null) {
                throw new Exception("Cannot access removed Clause.");
            }
            List<Clause> ithClauseAnteList = constructAntecedentsList(currIthClauseOrNull);
            IntIterator ithClauseLitsIt = currIthClauseOrNull.literals();
            List<Integer> ithClauseLits = new ArrayList<>();
            while (ithClauseLitsIt.hasNext()) {
                ithClauseLits.add(ithClauseLitsIt.next());
            }

            this.antecedents = ithClauseAnteList;
            this.literals = ithClauseLits;
			return this;
		}

        /**
         * Adds a new antecedent clause to the ClauseView.
         * @param newAnte The new antecedent clause to be added.
         */
        public void addAntecedent(Clause newAnte) {
            this.antecedents.add(newAnte);
        }
        

        @Override
        public int size() {
            return this.literals.size();
        }

        @Override
        public IntIterator literals() {
            int n = this.literals.size();
            int[] literalsArray = new int[n];
            for (int i = 0; i < n; i++) {
                literalsArray[i] = this.literals.get(i);
            }
            return new IntArrayIterator(literalsArray, 0, this.literals.size());
        }

        @Override
        public int maxVariable() {
            return StrictMath.abs(this.literals.get(this.literals.size() - 1));
        }

        @Override
        public int[] toArray(int[] array) {
            // TODO: REDO THIS 
            return array;
        }

        @Override
        public int numberOfAntecedents() {
            return this.antecedents.size();
        }

        @Override
        public Iterator<Clause> antecedents() {
            // TODO: fill this in
            return this.antecedents.iterator();
        }

    }

    /**
	 * A clause iterator wrapper for an int iterator.
	 * @author Emina Torlak
	 */
	private final class ClauseIterator extends ClauseView implements Iterator<Clause> {
		private final IntIterator itr;
		/**
		 * Constructs a clause iterator that will iterate over the clauses in this.trace
		 * located at the indices given by itr.  The given iterator must return valid indices.
		 */
		ClauseIterator(IntIterator itr) {
			this.itr = itr;
		}
		public boolean hasNext() { return itr.hasNext(); }
		public Clause next() { 
            try {
                return set(itr.next()); 
            } catch (NoSuchElementException ne) {
                throw ne;
            } catch (Exception e) {
                return this.next();
            }
        }
		public void remove() { throw new UnsupportedOperationException(); }
	}

    /**
	 * An int iterator that iterates over the portion of an integer array
	 * in the increasing order of indices.
	 * @author Emina Torlak
	 */
	private static final class IntArrayIterator implements IntIterator {
		private final int[] array;
		private int from;
		private final int to;	
		/**
		 * Constructs an int iterator that iterates over the given array,
		 * returning the elements between from, inclusive, and to, exclusive.
		 * @requires 0 <= from < array.length < Integer.MAX_VALUE
		 */
		IntArrayIterator(int[] array, int from, int to) {
			this.array = array;
			this.from = from;
			this.to = to;
		}
		public boolean hasNext() {	return from >= 0 && from < to; }
		public int next() {
			if (!hasNext()) throw new NoSuchElementException();
			return array[from++];
		}
		public void remove() {	throw new UnsupportedOperationException(); }	
	}
}