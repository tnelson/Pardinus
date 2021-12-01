package kodkod.engine.proofExplanation.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;

import kodkod.engine.satlab.Clause;
import kodkod.engine.satlab.ResolutionTrace;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.Ints;

public class ReducedResolutionTrace implements ResolutionTrace{
    
    public ReducedResolutionTrace(ResolutionTrace origTrace) {
        // TODO: fill this in
    }

    @Override
    public int size() {
        // TODO: fill this in
        return 1;
    }

    @Override
    public Iterator<Clause> iterator() {
        // TODO: fill this in
        return new ArrayList<Clause>().iterator();
    }


    @Override
    public Iterator<Clause> iterator(IntSet indices) {
        // TODO: fill this in
        return new ArrayList<Clause>().iterator();
    }

    @Override
    public Iterator<Clause> reverseIterator(IntSet indices) {
        // TODO: fill this in
        return new ArrayList<Clause>().iterator();
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
        return new ClauseView();
    }

    /**
     * A mutable implementation of the Clause interface
     * @author Swetabh Changkakoti
     */
    private class ClauseView extends Clause {

        ClauseView() {
            // TODO: fill this in
        }

        @Override
        public int size() {
            // TODO: fill this in
            return 1;
        }

        @Override
        public IntIterator literals() {
            // TODO: fill this in
            return new IntArrayIterator(new int[0], 0, 0);
        }

        @Override
        public int maxVariable() {
            // TODO: fill this in
            return 1;
        }

        @Override
        public int[] toArray(int[] array) {
            // TODO: fill this in
            return array;
        }

        @Override
        public int numberOfAntecedents() {
            // TODO: fill this in
            return 1;
        }

        @Override
        public Iterator<Clause> antecedents() {
            // TODO: fill this in
            return new ArrayList<Clause>().iterator();
        }

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