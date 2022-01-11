package kodkod.engine.proofExplanation.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
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
import java.util.Map.Entry;
import java.util.stream.Collectors;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.IntTreeSet;
import kodkod.util.ints.Ints;

/**
 * An implementation of the {@linkplain ResolutionTrace} interface inspired by
 * Emina Torlak's {@linkplain LazyTrace} implementation. Acts as a proxy for the interface
 * reducing a {@linkplain ResolutionTrace} according to a set of assumption literals.
 * In particular, this works top-down from the empty clause, removing branches and propagating
 * assumption literals on clauses as suitable. Uses the {@linkplain TraceNode}
 * extension of the {@linkplain Clause} abstract class to store reduced clauses.
 * NOTE: this currently does not have working implementations for reachable, backwardsReachable,
 * learnable, directlyLearnable.
 */
public class ReducedResolutionTrace implements ResolutionTrace {

    private ResolutionTrace origTrace;
    private Map<Integer, TraceNode> reducedClauseMap;
    private Clause[] reducedTrace;
    private final TraceNode EMPTY_CLAUSE = new TraceNode(new ArrayList<>(), new ArrayList<>());

    // traverses the trace breadth-first, starting from the empty clause, running our
    // reduced trace construction algorithm.
    public ReducedResolutionTrace(ResolutionTrace origTrace, IntSet assumps) {
        this.origTrace = origTrace;
        this.reducedClauseMap = new HashMap<>();
        Map<Integer, TraceNode> reducedTreeMap = new HashMap<>();
        Queue<Pair<Clause, Optional<Integer>>> bfsQueue = new LinkedList<>();
        Set<Integer> visited = new HashSet<>();

        // using reverse topological order iterator to access the final empty clause
        Iterator<Clause> reverseOrigClauseIterator = origTrace.reverseIterator();
        if (reverseOrigClauseIterator.hasNext()) {
            Pair<Clause, Optional<Integer>> root = new Pair<>(reverseOrigClauseIterator.next(), Optional.empty());
            if (assumps.isEmpty()) {
                setUpClonedClauseMap();
            } else {
                try {
                    this.reducedClauseMap = reductionProcess(root, bfsQueue, visited, reducedTreeMap, assumps);
                } catch (Exception e) {
                    System.err.println(e.getLocalizedMessage());
                }
            }
        }

        // fill in reducedTrace using the contents of reducedClauseMap
        List<Clause> reducedTraceList = new ArrayList<>();
        for (Iterator<Clause> origClauseIterator = origTrace.iterator(); origClauseIterator.hasNext(); ) {
            Clause origClause = origClauseIterator.next();
            if (reducedClauseMap.containsKey(origClause.hashCode())) {
                reducedTraceList.add(reducedClauseMap.get(origClause.hashCode()));
            }
        }
        
        this.reducedTrace = new Clause[reducedTraceList.size()];
        for (int i = 0; i < this.reducedTrace.length; i++) {
            this.reducedTrace[i] = reducedTraceList.get(i);
        }

    }

    /**
     * Sets up this.reducedClauseMap using origTrace, given that there are no assumptions being propagated.
     */
    private void setUpClonedClauseMap() {
        for (Iterator<Clause> origIt = origTrace.iterator(); origIt.hasNext(); ) {
            Clause clause = origIt.next();
            this.reducedClauseMap.put(clause.hashCode(), new TraceNode(clause));
        }
    }

    // TODO: document and potentially refactor
    private Map<Integer, TraceNode> reductionProcess (
        Pair<Clause, Optional<Integer>> currPair, 
        Queue<Pair<Clause, Optional<Integer>>> bfsQueue, Set<Integer> visited, 
        Map<Integer, TraceNode> reducedTraceMap, IntSet assumps) throws Exception {

        Clause currClause = currPair.getKey();
        int currHashCode = currClause.hashCode();
        Optional<Integer> parentHashOpt = currPair.getValue();
        List<Integer> currLiterals = constructLiteralsList(currClause);
        TraceNode currTraceNode = new TraceNode(currLiterals, new ArrayList<>());
        boolean containsAssump = false;
        TraceNode newParent = new TraceNode(currClause);

        // C == {} case:
        //    if C is an empty clause {}, push antecedents to queue. if no antecedents, move onto the queue.
        if (currLiterals.isEmpty()) {
            reducedTraceMap.put(currHashCode, currTraceNode);
            for (Iterator<Clause> anteIterator = currClause.antecedents(); anteIterator.hasNext(); ) {
                TraceNode anteTraceNode = new TraceNode(anteIterator.next());
                bfsQueue.add(new Pair<>(anteTraceNode, Optional.of(currHashCode)));
            }
            if (bfsQueue.isEmpty()) {
                return reducedTraceMap;
            } else {
                return reductionProcess(bfsQueue.poll(), bfsQueue, visited, reducedTraceMap, assumps);
            }
        } else {
            for (IntIterator assumpIterator = assumps.iterator(); assumpIterator.hasNext(); ) {
                int assump = assumpIterator.next();

                // C contains A case:
                //    if C contains A for any assump A, we simply ignore it and move on
                if (currLiterals.contains(assump)) {
                    containsAssump = true;
                    // transition: move on to next item of queue
                    break;
                }

                // C == -A case:
                //    if C is -A for any assump A, throw away tree so far, throw away queue, 
                //    and restart at empty clause and push on antecedents of C
                if ((currLiterals.size() == 1) && (currLiterals.get(0) == (-1 * assump))) {
                    Queue<Pair<Clause, Optional<Integer>>> newBfsQueue = new LinkedList<>();
                    for (Iterator<Clause> anteIterator = currClause.antecedents(); anteIterator.hasNext(); ) {
                        newBfsQueue.add(new Pair<>(anteIterator.next(), 
                            Optional.of(currHashCode))); // encoding current clause as parent
                    }
                    Map<Integer, TraceNode> newReducedTraceMap = new HashMap<>();
                    newReducedTraceMap.put(currHashCode, EMPTY_CLAUSE);
                    return reductionProcess(
                        new Pair<>(EMPTY_CLAUSE, Optional.empty()), newBfsQueue, visited, newReducedTraceMap, assumps);
                }

                // C is other clause case:
                //     if C is any other clause and unitProp(C, A) is parent, remove other children from queue
                //     else, add unitProp(C, A) to the tree, and push antecedents of C to the queue
                Optional<Clause> unitProppedClauseOpt = unitPropagateAllOpt(currClause, assumps);
                // given our prior checks, this should always be true
                if (unitProppedClauseOpt.isPresent()) {
                    List<Integer> unitProppedLiterals = constructLiteralsList(unitProppedClauseOpt.get());

                    // check literals equality with parent (this should happen if antecedents don't resolve)
                    if (parentHashOpt.isPresent() && (reducedTraceMap.containsKey(parentHashOpt.get()))) {
                        Integer parentHash = parentHashOpt.get();
                        TraceNode parentClause = reducedTraceMap.get(parentHash);
                        List<Integer> parentLiterals = constructLiteralsList(parentClause);
                        if (unitProppedLiterals.equals(parentLiterals)) {
                            parentClause.resetAntecedents();
                            // add to tree. remove elements of queue with same parent.
                            boolean queueContainsSiblings = true;
                            while (queueContainsSiblings) {
                                if (bfsQueue.isEmpty()) {
                                    break;
                                }
                                Optional<Integer> nextParent = bfsQueue.peek().getValue();
                                if (nextParent.isPresent() && nextParent.get().equals(parentHash)) {
                                    bfsQueue.poll();
                                } else {
                                    queueContainsSiblings = false;
                                }
                            }
                        }
                    }
                    
                    newParent = new TraceNode(unitProppedLiterals, new ArrayList<>());

                    // this check and potential replacement ensures that if there is a duplicate 
                    // of an ante clause, then we do not have different instances in the ante and leaf positions
                    if (reducedTraceMap.containsKey(currHashCode)) {
                        newParent = reducedTraceMap.get(currHashCode);
                    }
                    if (!visited.contains(currHashCode)) {
                        reducedTraceMap.put(currHashCode, newParent);
                    }
                    
                    for (Iterator<Clause> anteIterator = currClause.antecedents(); anteIterator.hasNext(); ) {
                        Clause nextAnte = anteIterator.next();
                        // TODO: not completely sure this check works
                        if (visited.contains(nextAnte.hashCode())) {
                            continue;
                        }
                        Pair<Clause, Optional<Integer>> newPair =  
                            new Pair<>(nextAnte, Optional.of(currHashCode));
                        bfsQueue.add(newPair);
                    }
                }
            }
        }

        if (parentHashOpt.isPresent() && !containsAssump) {
            int parentHash = parentHashOpt.get();
            TraceNode parentTraceNode;
            if (reducedTraceMap.containsKey(parentHash)) {
                parentTraceNode = reducedTraceMap.get(parentHash);
            } else {
                // we only get to this case if we were previously in a C == -A case,
                // in which case the assigned parent should be changed to the empty clause
                
                // look for empty clause and get its hashCode
                parentTraceNode = reducedTraceMap.get(0);
                for (TraceNode tn : reducedTraceMap.values()) {
                    if (tn.size() == 0) {
                        parentTraceNode = tn;
                    }
                }
            }

            boolean anteAlreadyPresent = false;
            for (Iterator<Clause> parentAntes = parentTraceNode.antecedents(); parentAntes.hasNext(); ) {
                if (parentAntes.next().equals(newParent)) {
                    anteAlreadyPresent = true;
                }
            }
            if (!anteAlreadyPresent) {
                parentTraceNode.addAntecedent(newParent);
            }
        }

        // if bfsQueue is not empty, move on to the next entry
        if (!bfsQueue.isEmpty()) {
            Pair<Clause, Optional<Integer>> nextPair = bfsQueue.poll();
            if (!currLiterals.isEmpty()) {
                visited.add(currHashCode);
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
        List<TraceNode> antecedents = this.constructAntecedentsList(clause)
            .stream()
            .map(TraceNode::new)
            .collect(Collectors.toList());

        return Optional.of(new TraceNode(newLiterals, antecedents));
    }

    /**
     * Constructs a {@linkplain List} of antecedent {@linkplain Clause} objects for the given clause,
     * in the order in which they appear in the clause's {@linkplain Clause#antecedents()} output.
     * @param clause The clause to construct an antecedents list for.
     * @return The constructed list of clauses.
     */
    private List<Clause> constructAntecedentsList(Clause clause) {
        List<Clause> antecedents = new ArrayList<>();
        for (Iterator<Clause> antecedentsIt = clause.antecedents(); antecedentsIt.hasNext(); ) {
            antecedents.add(antecedentsIt.next());
        }
        return antecedents;
    }

    /**
     * Constructs a {@linkplain List} of the input clause's literals in an arbitrary order.
     * @param clause The clause to construct a literals list for.
     * @return The constructed list of literals.
     */
    private List<Integer> constructLiteralsList(Clause clause) {
        List<Integer> lits = new ArrayList<>();
        for (IntIterator litIt = clause.literals(); litIt.hasNext(); ) {
            lits.add(litIt.next());
        }
        return lits;
    }
    

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#size()
	 */
    public int size() {
        return reducedTrace.length;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#core()
	 */
    public IntSet core() {
        IntSet origCore = origTrace.core();
        return getUpdatedIndices(origCore);
    }

    /**
	 * {@inheritDoc}
     * NOTE: by definition, core() and axioms() have the exact same behavior for ReducedResolutionTrace.
	 * @see kodkod.engine.satlab.ResolutionTrace#axioms()
	 */
    public IntSet axioms() {
        IntSet origAxioms = origTrace.axioms();
        return getUpdatedIndices(origAxioms);
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#resolvents()
	 */
    public IntSet resolvents() {
        IntSet origResolvents = origTrace.resolvents();
        return getUpdatedIndices(origResolvents);
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#iterator()
	 */
    public Iterator<Clause> iterator() {
        List<Clause> trace = Arrays.asList(reducedTrace);
        return trace.iterator();
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#reverseIterator()
	 */
	public Iterator<Clause> reverseIterator() { 
		List<Clause> trace = Arrays.asList(reducedTrace);
        Collections.reverse(trace);
        return trace.iterator();
	}

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#core(IntSet)
	 */
    public Iterator<Clause> iterator(IntSet indices) {
        Iterator<Integer> idxIterator = orderedIntIterator(indices, (a, b) -> a.compareTo(b) );
        return new Iterator<Clause>() {
            public boolean hasNext() {
                return idxIterator.hasNext();
            }
            public Clause next() throws NoSuchElementException {
                // NOTE: this is error-prone
                int nextInd = idxIterator.next();
                try {
                    return reducedTrace[nextInd];
                } catch (IndexOutOfBoundsException ie) {
                    throw new NoSuchElementException("Index absent in reduced trace: " + nextInd);
                }
            }
        };
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#reverseIterator(IntSet)
	 */
    public Iterator<Clause> reverseIterator(IntSet indices) {
        Iterator<Integer> idxIterator = orderedIntIterator(indices, (a, b) -> b.compareTo(a) );
        return new Iterator<Clause>() {
            public boolean hasNext() {
                return idxIterator.hasNext();
            }
            public Clause next() throws NoSuchElementException {
                // NOTE: this is error-prone
                int nextInd = idxIterator.next();
                try {
                    return reducedTrace[nextInd];
                } catch (IndexOutOfBoundsException ie) {
                    throw new NoSuchElementException("Index absent in reduced trace: " + nextInd);
                }
            }
        };
    }

    /**
     * Creates an iterator over the elements of a given {@linkplain IntSet} such that they
     * appear sorted in an order determined by a given {@linkplain Comparator}.
     * @param elements The {@linkplain IntSet} of elements to iterate over.
     * @param comp The {@linkplain Comparator} determining the ordering of elements in the iterator.
     * @return An {@linkplain Iterator} of Integers in the input, sorted according 
     * to the input {@linkplain Comparator}
     */
    private Iterator<Integer> orderedIntIterator(IntSet elements, Comparator<Integer> comp) {
        List<Integer> orderedElts = new ArrayList<>();
        for (IntIterator eltIt = elements.iterator(); eltIt.hasNext(); ) {
            orderedElts.add(eltIt.next());
        }
        Collections.sort(orderedElts, comp);

        return orderedElts.iterator();
    }

    /**
     * Keeps only those indices from a list of indices that correspond to clauses
     * in the reduced trace.
     * @param origIndices The original {@linkplain IntSet} of indices.
     * @return A IntSet representing the updated indices.
     */
    private IntSet getUpdatedIndices(IntSet origIndices) {
        IntSet updatedIndices = new IntTreeSet();
        
        for (IntIterator origIndicesIt = origIndices.iterator(); origIndicesIt.hasNext(); ) {
            int origIndex = origIndicesIt.next();
            Clause origClause = origTrace.get(origIndex);
            if (reducedClauseMap.containsKey(origClause.hashCode())) {
                updatedIndices.add(origIndex);
            }
        }
        return updatedIndices;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#get(int)
	 */
    public Clause get(int index) {
        return reducedTrace[index];
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#reachable(IntSet)
	 */
    public IntSet reachable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#backwardReachable(IntSet)
	 */
    public IntSet backwardReachable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#learnable(IntSet)
	 */
    public IntSet learnable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }

    /**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.ResolutionTrace#directlyLearnable(IntSet)
	 */
    public IntSet directlyLearnable(IntSet indices) {
        // TODO: fill this in
        return Ints.EMPTY_SET;
    }
    
    
}