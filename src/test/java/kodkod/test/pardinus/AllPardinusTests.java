package kodkod.test.pardinus;

import kodkod.test.pardinus.decomp.AllDecompTests;
import kodkod.test.pardinus.symbolic.AllSymbolicTests;
import kodkod.test.pardinus.temporal.AllTemporalTests;
import kodkod.test.pardinus.unbounded.AllUnboundedTests;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	AllDecompTests.class,
	AllTemporalTests.class,
	AllSymbolicTests.class,
	AllUnboundedTests.class,
})

public class AllPardinusTests {}
