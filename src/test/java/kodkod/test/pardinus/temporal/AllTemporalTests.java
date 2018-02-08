package kodkod.test.pardinus.temporal;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
	SymmetryTests.class,
    TemporalTranslatorTests.class,
    NNFUnitTesting.class,
    TemporalSlicerUnitTesting.class
})

public class AllTemporalTests {}
