package kodkod.engine.proofExplanation.core;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

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

    // contains a mapping from the old clauses to their updated versions in the reduced trace.
    // this need not contain all the clauses from the original trace as keys, since some might
    // be removed during reduction.
    // NOTE: this also means it's important to ensure that the key clauses aren't being mutated 
    // at any point.
    private Map<Integer, Clause> reducedClauseMap;
    //private Map<Set<Integer>, Clause> reducedClauseMap;

    private ResolutionTrace origTrace;
    private Clause[] reducedTrace;

    // TODO: check this - do we need to map each Clause to its index in the original trace to be
    //  - able to return core, resolved, axioms as IntSets?
    //  - OR: can we get the original answers, check for which clauses end up in `reducedClauseMap`,
    //  - and only keep the indices of the ones that do?
    
    public ReducedResolutionTrace(ResolutionTrace origTrace, IntSet assumps) {

        this.origTrace = origTrace;
        //this.reducedClauseMap = new HashMap<Integer, Clause>();
        this.reducedClauseMap = new HashMap<Integer, Clause>();

        // if we are operating on Clauses, then trace.iterator() gives us the Clauses
        // of the trace "in order", i.e. in a topologically sorted order
        Iterator<Clause> origClauseIterator = origTrace.iterator();

        int i = 0;
        // note that on first pass of edgePlanIterator, we can also tell which Clauses
        // are axioms, and can integrate the unit propagation step in that pass
        Clause currClause, updatedClause;

        while (origClauseIterator.hasNext()) {
            currClause = origClauseIterator.next();
            // print reducedClauseMap keySet to debug
            //System.out.println("VALUES AT BEGINNING OF ITERATION: ");
            //for (Clause v : this.reducedClauseMap.values()) {
            //    System.out.println(":: " + v);
            //}
            //System.out.println("~~~~");
            boolean isAxiom = (currClause.numberOfAntecedents() == 0);
            if (isAxiom) {
                Optional<Clause> updatedClauseOpt = unitPropagateAllOpt(currClause, assumps);
                // add mapping from old clause to updated clause if the former doesn't reduce to
                // true upon updating. 
                if (updatedClauseOpt.isPresent()) {
                    //System.out.println(reducedClauseMap.size());
                    updatedClause = updatedClauseOpt.get();
                    // building set of literals
                    IntIterator litIterator = currClause.literals();
                    Set<Integer> litSet = new HashSet<Integer>();
                    while (litIterator.hasNext()) {
                        litSet.add(litIterator.next());
                    }
                    //reducedClauseMap.put(currClause.hashCode(), updatedClause);
                    reducedClauseMap.put(litSet.hashCode(), updatedClause);
                }
                // do nothing in the axiom case if not present
            } else {
                try {
                    System.out.println("Clause was previously: " + currClause);
                    System.out.println("Original clause's antecedents: ");
                    Iterator<Clause> origAntecedents = currClause.antecedents();
                    while (origAntecedents.hasNext()) {
                        System.out.println(origAntecedents.next());
                    }
                    Optional<Clause> resolvedClauseOpt = resolveAntecedents(origTrace, currClause);
                    System.out.println("resolvedClauseOpt: " + resolvedClauseOpt);
                    if (resolvedClauseOpt.isPresent()) {
                        Clause resolvedClause = resolvedClauseOpt.get();
                        System.out.println("Clause is now: " + resolvedClause);
                        // building set of literals
                        IntIterator litIterator = currClause.literals();
                        Set<Integer> litSet = new HashSet<Integer>();
                        while (litIterator.hasNext()) {
                            litSet.add(litIterator.next());
                        }
                        //reducedClauseMap.put(currClause.hashCode(), resolvedClause);
                        reducedClauseMap.put(litSet.hashCode(), resolvedClause);
                        // if literals is empty, we have reached UNSAT, and we stop adding clauses
                        // at that point
                        // TODO: ^ is what we're doing in the UNSAT case the right thing?
                        if (resolvedClause.size() == 0) {
                            break;
                        }
                    }
                    // if resolvedClauseOpt is empty, there are two possibilities:
                    //  1. the updated antecedents of the new clause do not resolve, and thus 
                } catch (Exception e) { // error occurs if none of the antecedents are in map
                    // do nothing in this case and move on.
                }
            }
            i++;
        }

        // fill in the reducedTrace array in order using reducedClauseMap
        this.reducedTrace = new Clause[origTrace.size() + 1];
        origClauseIterator = origTrace.iterator();
        int itIndex = 0;
        while (origClauseIterator.hasNext()) {
            //this.reducedTrace[itIndex] = reducedClauseMap.get(origClauseIterator.next());
            Clause origClause = origClauseIterator.next();
            // building set of literals
            IntIterator litIterator = origClause.literals();
            Set<Integer> litSet = new HashSet<Integer>();
            while (litIterator.hasNext()) {
                litSet.add(litIterator.next());
            }
            Clause updatedClauseOrNull = reducedClauseMap.get(litSet.hashCode());
            if (updatedClauseOrNull != null) {
                this.reducedTrace[itIndex] = updatedClauseOrNull;
                //System.out.println(updatedClauseOrNull);
                itIndex++;
            }
        }
        
        // asserting that each value in the reducedClauseMap is in the reducedTrace array
        Collection<Clause> reducedClauses = new ArrayList<Clause>(reducedClauseMap.values());
        for (Clause c : reducedTrace) {
            if (reducedClauses.contains(c)) {
                reducedClauses.remove(c);
            }
        }
        assert reducedClauses.isEmpty();
        
        List<Integer> exampleList1 = new ArrayList<>();
        List<Integer> exampleList2 = new ArrayList<>();
        List<Integer> exampleList3 = new ArrayList<>();
        exampleList1.add(-1);
        exampleList1.add(2);
        exampleList2.add(-1);
        exampleList2.add(-2);
        List<List<Integer>> lls = new ArrayList<>();
        lls.add(exampleList1);
        lls.add(exampleList2);
        //lls.add(exampleList3);
        
        System.out.println("Output of resolution example: ");
        System.out.println(this.resolveListOfLiteralLists(lls));
        
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
    private Optional<Clause> resolveAntecedents(ResolutionTrace origTrace, Clause clause) throws Exception {
        // get antecedents
        Iterator<Clause> origAntecedents = clause.antecedents();
        // get updated versions of antecedents
        List<Clause> newAntecedents = new ArrayList<Clause>();
        while (origAntecedents.hasNext()) {
            Clause currAntecedent = origAntecedents.next();
            System.out.println("Old Antecedent: " + currAntecedent);
            // building set of literals
            IntIterator litIterator = currAntecedent.literals();
            Set<Integer> litSet = new HashSet<Integer>();
            while (litIterator.hasNext()) {
                litSet.add(litIterator.next());
            }
            Clause updatedAntecedent = reducedClauseMap.get(litSet.hashCode());
            if (updatedAntecedent != null) {
                newAntecedents.add(updatedAntecedent);
            }
        }
        if (newAntecedents.isEmpty()) {
            throw new Exception("All original antecedents were removed; cannot resolve.");
        }
        for (Clause newAnte : newAntecedents) {
            System.out.println("New Antecedent: " + newAnte);
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
        // REMOVE THIS
        System.out.println("Literal lists being resolved:");
        for (List<Integer> ll : literalLists) {
            for (int li : ll) {
                System.out.print(li + ", ");
            }
            System.out.println();
        }
        System.out.println();

        // resolve the literals lists together and return
        Optional<List<Integer>> resolvedLiteralsOpt = resolveListOfLiteralLists(literalLists);
        if (resolvedLiteralsOpt.isPresent()) {
            Clause returnClause = new ClauseView(newAntecedents, resolvedLiteralsOpt.get());
            return Optional.of(returnClause);
        } else {
            return Optional.empty();
        }
    }

    /**
     * Given a list of lists of integers representing literals, this resolves all of the literal
     * lists together and returns the resolved list.
     * NOTE: This function assumes that the input list is not empty.
     * @param literalLists
     * @return
     */
    private Optional<List<Integer>> resolveListOfLiteralLists(List<List<Integer>> literalLists) {
        assert !literalLists.isEmpty();
        List<Integer> firstLits = literalLists.get(0);
        List<List<Integer>> listsToCheck = new ArrayList<List<Integer>>();
        for (int i = 1; i < literalLists.size(); i++) {
            listsToCheck.add(literalLists.get(i));
        }
        // this intends to keep redundant resolutions like {2} -> {2} in lieu of not handling changing indices
        //if (literalLists.size() == 1) {
        //    return Optional.of(literalLists.get(0));
        //}
        return runResolveTillFixedPoint(firstLits, listsToCheck, new ArrayList<List<Integer>>(), literalLists.size());
    }

    // TODO: document
    private Optional<List<Integer>> runResolveTillFixedPoint(List<Integer> litsToCompare,
                                                   List<List<Integer>> listsToCheck,
                                                   List<List<Integer>> listsCompared, int totalNumLists) {
        // if no more lists to check, that means all lists have been compared without resolution in
        // any comparison. this is equivalent to reaching fixed point, so the process can terminate here.
        System.out.println("Lits to compare: " + litsToCompare);                                               
        if (listsToCheck.isEmpty()) {
            List<Integer> returnList = new ArrayList<Integer>();
            for (List<Integer> lits : listsCompared) {
                for (int lit : lits) {
                    if (!returnList.contains(lit)) {
                        returnList.add(lit);
                    }
                }
            }
            // end condition when no resolution occurs:
            // listsToCheck is empty and there has been no change from the original in number of lists
            if (listsCompared.size() == totalNumLists - 1) {
                // no res => we return Optional.empty, since resolution cannot return a meaningful, non-empty result
                return Optional.empty();
            } else {
                for (int lit : litsToCompare) {
                    returnList.add(lit);
                }
                Collections.sort(returnList);
                return Optional.of(returnList);
            }
            
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
                return runResolveTillFixedPoint(currResolved, newListsToCheck, new ArrayList<List<Integer>>(), totalNumLists);
            }
        }
        List<Integer> newFirst = listsToCheck.remove(0);
        // TODO: check if the in-place edits are causing problems
        listsCompared.add(litsToCompare);
        return runResolveTillFixedPoint(newFirst, listsToCheck, listsCompared, totalNumLists);
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
                if (!resolvedList.contains((Integer) i)) {
                    resolvedList.add(i);
                }
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

    @Override
    public Clause get(int index) {
        Clause currClause = origTrace.get(index);
        // building set of literals
        IntIterator litIterator = currClause.literals();
        Set<Integer> litSet = new HashSet<Integer>();
        while (litIterator.hasNext()) {
            litSet.add(litIterator.next());
        }
        //return reducedClauseMap.get(origTrace.get(index));
        return reducedClauseMap.get(litSet.hashCode());
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
            IntIterator litIterator = origIthClause.literals();
            Set<Integer> litSet = new HashSet<Integer>();
            while (litIterator.hasNext()) {
                litSet.add(litIterator.next());
            }
            Clause currIthClauseOrNull = reducedClauseMap.get(litSet.hashCode());
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