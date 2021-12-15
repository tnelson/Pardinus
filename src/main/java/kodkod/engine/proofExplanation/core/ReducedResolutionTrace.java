package kodkod.engine.proofExplanation.core;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
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
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import javafx.util.Pair;
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

    private Clause[] reducedTrace;
    private final ClauseView EMPTY_CLAUSE = new ClauseView(new ArrayList<>(), new ArrayList<>());

    // traverses the trace breadth-first, starting from the empty clause, running our
    // reduced trace construction algorithm.
    public ReducedResolutionTrace(ResolutionTrace origTrace, IntSet assumps) {
        Map<Integer, ClauseView> reducedTraceMap = new HashMap<>();        
        Queue<ClauseView> bfsQueue = new LinkedList<>();
        Set<ClauseView> visited = new HashSet<>();

        Iterator<Clause> reverseOrigClauseIterator = origTrace.reverseIterator();
        if (reverseOrigClauseIterator.hasNext()) {
            Clause root = reverseOrigClauseIterator.next();

        }
    }

    // TODO: document
    private Map<Integer, ClauseView> reductionProcess(Pair<Clause, Optional<Integer>> currPair, 
        Queue<Pair<Clause, Optional<Integer>>> bfsQueue, Set<Clause> visited, Map<Integer, ClauseView> reducedTraceMap, IntSet assumps) {

            Clause currClause = currPair.getKey();
            Optional<Integer> parentHashOpt = currPair.getValue();
            List<Integer> currLiterals = constructLiteralsList(currClause);
            Clause treeClause = currClause;

            // C == {} case:
            //    if C is an empty clause {}, don't do anything on it and move straight to the queue
            if (!currLiterals.isEmpty()) {
                IntIterator assumpIterator = assumps.iterator();
                while (assumpIterator.hasNext()) {
                    int assump = assumpIterator.next();
    
                    // C contains A case:
                    //    if C contains A for any assump A, we simply ignore it and move on
                    if (currLiterals.contains(assump)) {
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
                    //     if C is any other clause, add unitProp(C, A) to the tree, and push antecedents of C to the queue
                    Optional<Clause> unitProppedClauseOpt = unitPropagateAllOpt(currClause, assumps);
                    // given our prior checks, this should always be true
                    if (unitProppedClauseOpt.isPresent()) {
                        Clause unitProppedClause = unitProppedClauseOpt.get();
                        // TODO: fix
                        reducedTraceMap.put(unitProppedClause.hashCode(), unitProppedClause);
                        Iterator<Clause> anteIterator = currClause.antecedents();
                        while (anteIterator.hasNext()) {
                            // TODO: if we're dealing with hashCodes, what should currClause be replaced with, if anything?
                            Pair<Clause, Optional<Integer>> newPair = new Pair<>(anteIterator.next(), Optional.of(currClause.hashCode()));
                            bfsQueue.add(newPair);
                        }
                    }
                }
    
            }

            
            // if the bfsQueue is empty, then return the current tree
            if (bfsQueue.isEmpty()) {
                return reducedTraceMap;
            }

            // if bfsQueue is not empty, move on to the next entry
            Pair<Clause, Optional<Integer>> nextPair = bfsQueue.poll();
            visited.add(currClause);
            if (parentHashOpt.isPresent()) {
                int parentHash = parentHashOpt.get();
                ClauseView parentClauseView = reducedTraceMap.get(parentHash);
                parentClauseView.addAntecedent(currClause);
            }

            return reductionProcess(nextPair, bfsQueue, visited, reducedTraceMap, assumps);
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
        List<Clause> antecedents = new ArrayList<Clause>();
        while (antecedentsIt.hasNext()) {
            antecedents.add(antecedentsIt.next());
        }
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
    
    
    /**
     * A mutable implementation of the Clause interface.
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
            Clause currIthClauseOrNull = reducedClauseMap.get(origIthClause);
            if (currIthClauseOrNull == null) {
                throw new Exception("Cannot access removed Clause.");
            }
            List<Clause> ithClauseAnteList = constructAntecedentsList(currIthClauseOrNull);
            IntIterator ithClauseLitsIt = currIthClauseOrNull.literals();
            List<Integer> ithClauseLits = new ArrayList<Integer>();
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