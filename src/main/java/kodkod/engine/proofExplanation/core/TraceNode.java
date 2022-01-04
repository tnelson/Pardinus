package kodkod.engine.proofExplanation.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.stream.Collectors;

import kodkod.engine.satlab.Clause;
import kodkod.util.ints.IntIterator;

/**
 * An extension of the {@linkplain Clause} abstract class to serve as a
 * raw {@linkplain Clause} that is not dependent on a larger {@linkplain ResolutionTrace}.
 */
public class TraceNode extends Clause {
    
    private List<Integer> literals;
    private List<TraceNode> antecedents;

    public TraceNode(List<Integer> lits, List<TraceNode> antes) {
        this.literals = lits;
        this.antecedents = antes;
    }

    public TraceNode(Clause clause) {
        this.antecedents = new ArrayList<>();
        this.literals = constructLiteralsList(clause);
        // deep tree copy, building TraceNodes at the bottom first 
        // and working upwards
        Iterator<Clause> topLevelAntes = clause.antecedents();
        if (topLevelAntes.hasNext()) {
            while (topLevelAntes.hasNext()) {
                Clause currAnte = topLevelAntes.next();
                
                // confirm that this recursion works
                this.antecedents.add(new TraceNode(currAnte));
            }
        } else {
            // base case: no antecedents, just assign literals.
            this.antecedents = new ArrayList<>();
        }
    }

    private List<Integer> constructLiteralsList(Clause clause) {
        IntIterator litIt = clause.literals();
        List<Integer> lits = new ArrayList<>();
        while (litIt.hasNext()) {
            lits.add(litIt.next());
        }
        return lits;
    }

    // EXISTS FOR DEBUGGING PURPOSES, REMOVE THIS
    public Iterator<TraceNode> traceNodeAntes() {
        return this.antecedents.iterator();
    }

    public void addAntecedent(TraceNode antecedent) {
        this.antecedents.add(antecedent);
    }

    public void resetAntecedents() {
        this.antecedents = new ArrayList<>();
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
        // relies on this.literals being sorted
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
        return this.antecedents.stream()
        .map(Clause.class::cast)
        .collect(Collectors.toList())
        .iterator();
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

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof TraceNode)) {
            return false;
        }

        TraceNode otherTN = (TraceNode) other;
        List<Integer> otherLiterals = constructLiteralsList(otherTN);
        // compare equality between literal and antecedents
        Iterator<Clause> otherAntes = otherTN.antecedents();
        Iterator<Clause> antes = this.antecedents();
        while (otherAntes.hasNext() && antes.hasNext()) {
            if (!otherAntes.next().equals(antes.next())) {
                return false;
            }
        }
        if (otherAntes.hasNext() || antes.hasNext()) {
            return false;
        }
        
        return this.literals.equals(otherLiterals);
    }

    @Override
    public int hashCode() {
        return super.hashCode();
    }

}
