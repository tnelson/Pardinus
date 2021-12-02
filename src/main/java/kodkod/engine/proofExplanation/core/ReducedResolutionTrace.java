package kodkod.engine.proofExplanation.core;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
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

    // contains a mapping from the old clauses to their updated versions in the reduced trace.
    // this need not contain all the clauses from the original trace as keys, since some might
    // be removed during reduction.
    // NOTE: this also means it's important to ensure that the key clauses aren't being mutated 
    // at any point.
    private Map<Clause, Clause> reducedClauseMap;

    private Clause[] reducedTrace;
    private IntSet core, resolved;
    private int axioms;
    
    public ReducedResolutionTrace(ResolutionTrace origTrace, IntSet assumps) {

        // if we are operating on Clauses, then trace.iterator() gives us the Clauses
        // of the trace "in order", i.e. in a topologically sorted order
        Iterator<Clause> origClauseIterator = origTrace.iterator();

        // note that on first pass of edgePlanIterator, we can also tell which Clauses
        // are axioms, and can integrate the unit propagation step in that pass
        while (origClauseIterator.hasNext()) {
            Clause currClause = origClauseIterator.next();
            boolean isAxiom = (currClause.numberOfAntecedents() == 0);
            if (isAxiom) {
                Optional<Clause> updatedClauseOpt = unitPropagateAllOpt(currClause, assumps);
                // add mapping from old clause to updated clause if the former doesn't reduce to
                // true upon updating. 
                if (updatedClauseOpt.isPresent()) {
                    reducedClauseMap.put(currClause, updatedClauseOpt.get());
                } else {

                }
            } else {
                try {
                    Clause resolvedClause = resolveAntecedents(origTrace, currClause);
                    reducedClauseMap.put(currClause, resolvedClause);
                    // if literals is empty, we have reached UNSAT, and we stop adding clauses
                    // at that point
                    // TODO: ^ is what we're doing in the UNSAT case the right thing?
                    if (resolvedClause.size() == 0) {
                        break;
                    }
                } catch (Exception e) { // error occurs if none of the antecedents are in map
                    // do nothing in this case and move on.
                }
            }
        }

        // fill in the reducedTrace array in order using reducedClauseMap
        reducedTrace = new Clause[reducedClauseMap.size()];
        origClauseIterator = origTrace.iterator();
        int itIndex = 0;
        while (origClauseIterator.hasNext()) {
            reducedTrace[itIndex] = reducedClauseMap.get(origClauseIterator.next());
            itIndex++;
        }

        // TODO: will need to build in index handling again. The current construction handles building
        //  - the Clause[] but has no solution for the .core(), .resolved(), .axioms() methods, since
        //  - those return IntSets, not lists of Clauses

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

    // TODO: consider switching back to arrays from lists; the next function is super inefficient

    /**
     * Given an original {@linkplain ResolutionTrace} and a {@linkplain Clause} from this original
     * trace, this returns a new clause made by resolving the updated versions of the original clause's 
     * antecedents. 
     * NOTE: this assumes that at least one of the input {@linkplain Clause}'s original antecedents is
     * in the reducedClauseMap.
     * @param origTrace The original {@linkplain ResolutionTrace} in reference.
     * @param clause The clause whose antecedents this function wishes to resolve.
     * @return An Optional containing the resolved clause if it is non-empty and empty if it is.
     * @throws Exception if none of the input clause's antecedents were are present in the updated map.
     */
    private Clause resolveAntecedents(ResolutionTrace origTrace, Clause clause) throws Exception {
        // get antecedents
        Iterator<Clause> origAntecedents = clause.antecedents();
        // get updated versions of antecedents
        List<Clause> newAntecedents = new ArrayList<Clause>();
        while (origAntecedents.hasNext()) {
            Clause currAntecedent = origAntecedents.next();
            Clause updatedAntecedent = reducedClauseMap.get(currAntecedent);
            if (updatedAntecedent != null) {
                newAntecedents.add(updatedAntecedent);
            }
        }
        if (newAntecedents.isEmpty()) {
            throw new Exception("All original antecedents were removed; cannot resolve.");
        }
        // get literal lists from antecedents
        List<List<Integer>> literalLists = new ArrayList<List<Integer>>();
        for (Clause ante : newAntecedents) {
            IntIterator litIterator = ante.literals();
            List<Integer> litList = new ArrayList<Integer>();
            while (litIterator.hasNext()) {
                litList.add(litIterator.next());
            }
            literalLists.add(litList);
        }
        // resolve the literals lists together and return
        List<Integer> resolvedLiterals = resolveListofLiteralLists(literalLists);
        return new ClauseView(newAntecedents, resolvedLiterals);
    }

    /**
     * Given a list of lists of integers representing literals, this resolves all of the literal
     * lists together and returns the resolved list.
     * NOTE: This function assumes that the input list is not empty.
     * @param literalLists
     * @return
     */
    private List<Integer> resolveListofLiteralLists(List<List<Integer>> literalLists) {
        assert !literalLists.isEmpty();
        List<Integer> firstLits = literalLists.get(0);
        List<List<Integer>> listsToCheck = new ArrayList<List<Integer>>();
        for (int i = 1; i < literalLists.size(); i++) {
            listsToCheck.add(literalLists.get(i));
        }
        return runResolveTillFixedPoint(firstLits, listsToCheck, new ArrayList<List<Integer>>());
    }

    // TODO: document
    private List<Integer> runResolveTillFixedPoint(List<Integer> litsToCompare,
                                                   List<List<Integer>> listsToCheck,
                                                   List<List<Integer>> listsCompared) {
        // if no more lists to check, that means all lists have been compared without resolution in
        // any comparison. this is equivalent to reaching fixed point, so the process can terminate here.                                               
        if (listsToCheck.isEmpty()) {
            List<Integer> returnList = new ArrayList<Integer>();
            for (List<Integer> lits : listsCompared) {
                for (int lit : lits) {
                    if (!returnList.contains(lit)) {
                        returnList.add(lit);
                    }
                }
            }
            return returnList;
        }
        Iterator<List<Integer>> listsToCheckIt = listsToCheck.iterator();

        // go over the lits lists that haven't been checked yet and compare the current lits with
        // them. if resolve happens, update list and rerun, else add check the rest of listsToCheck
        // with what was previously its first element
        while (listsToCheckIt.hasNext()) {
            List<Integer> currLits = listsToCheckIt.next();
            Optional<List<Integer>> currResolvedOpt = resolveTwoLiteralLists(litsToCompare, currLits);
            if (currResolvedOpt.isPresent()) {
                List<Integer> currResolved = currResolvedOpt.get();
                listsToCheckIt.remove();
                Iterable<List<Integer>> listsToCheckIterable = () -> listsToCheckIt;
                List<List<Integer>> newListsToCheck = StreamSupport
                                                        .stream(listsToCheckIterable.spliterator(), false)
                                                        .collect(Collectors.toList());
                return runResolveTillFixedPoint(currResolved, newListsToCheck, new ArrayList<List<Integer>>());
            }
        }
        List<Integer> newFirst = listsToCheck.remove(0);
        // TODO: check if the in-place edits are causing problems
        listsCompared.add(litsToCompare);
        return runResolveTillFixedPoint(newFirst, listsToCheck, listsCompared);
    }

    /**
     * Given two Lists of integers (representing literals), produces an Optional of the
     * new resolved list of integers, where a value being present in the Optional indicates
     * that a resolution has occurred.
     * @param list1 One of the two Lists of literals.
     * @param list2 The other of the two Lists of literals.
     * @return An Optional containing the resolved List of literals if resolution has occurred.
     */
    private Optional<List<Integer>> resolveTwoLiteralLists(List<Integer> list1, List<Integer> list2) {
        List<Integer> resolvedList = new ArrayList<Integer>();
        boolean resolved = false;
        for (int i : list1) {
            if (resolved || !list2.remove((Integer) (-1 * i))) {
                resolvedList.add(i);
            } else {
                resolved = true;
            }
        }
        if (resolved) {
            for (int i : list2) {
                resolvedList.add(i);
            }
            return Optional.of(resolvedList);
        } else {
            return Optional.empty();
        }
    }

    @Override
    public int size() {
        return reducedTrace.length;
    }

    @Override
    public Iterator<Clause> iterator() {
        return new ClauseIterator(new IntIterator() {
			int index = 0;
			public boolean hasNext() { return index>=0 && index < reducedTrace.length; }
			public int next() { 
				if (!hasNext()) throw new NoSuchElementException();
				return index++;
			}
			public void remove() { throw new UnsupportedOperationException(); } 
		});
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

    @Override
    public IntSet core() {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    @Override
    public IntSet axioms() {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    @Override
    public IntSet resolvents() {
        // TODO: fill this in
        return Ints.EMPTY_SET;
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

    @Override
    public Clause get(int index) {
        // TODO: fill this in
        return null;
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

        
        /**
		 * Sets the state of this clause view to represent
		 * the ith clause in the trace and returns this.
		 * @ensures sets the state of this clause view to represent
		 * the ith clause in the trace
		 * @return this
		 */
        /*
		ClauseView set(int index) {
			this.clauseIndex = index;
            // TODO: does this need more?
			return this;
		}
        */

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
		public Clause next() { return set(itr.next()); }
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