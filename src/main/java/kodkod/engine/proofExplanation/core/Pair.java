package kodkod.engine.proofExplanation.core;

/**
 * A generically typed Pair class that contains a key and a value.
 * Modelled after javafx.util.Pair.
 */
public class Pair<A, B> {
    private A a;
    private B b;

    public Pair(A a, B b) {
        this.a = a;
        this.b = b;
    }

    public A getKey() {
        return this.a;
    }

    public B getValue() {
        return this.b;
    }

    @Override
    public String toString() {
        return "< " + a + ", " + b + " >";
    }
}