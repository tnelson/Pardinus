package kodkod.test.pardinus.temporal;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	BaseTests.class,
	InstanceExpansionTests.class,
	NNFUnitTesting.class,
	PastUnrollingTests.class,
    TemporalSlicerUnitTesting.class,
    TemporalTranslatorTests.class,
    ExampleTests.class,
})

public class AllTemporalTests {}
