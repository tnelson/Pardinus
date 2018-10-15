package kodkod.test.pardinus.temporal;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	InstanceExpansionTests.class,
	NNFUnitTesting.class,
	PastUnrollingTests.class,
    TemporalSlicerUnitTesting.class,
    TemporalTranslatorTests.class
})

public class AllTemporalTests {}
