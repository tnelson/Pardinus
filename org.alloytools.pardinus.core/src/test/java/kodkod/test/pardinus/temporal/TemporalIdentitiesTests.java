/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertFalse;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * A set of LTL identities that must hold for all backends (within reasonable
 * trace lengths for bounded ones).
 * 
 * @author Nuno Macedo // [pardinus] temporal model finding
 *
 */
@RunWith(Parameterized.class)
public class TemporalIdentitiesTests {
	private PardinusSolver dsolver;
	private ExtendedOptions opt;
	static private Relation g = Relation.unary_variable("g"), h = Relation.unary_variable("h"), i  = Relation.unary_variable("i");
	static private Formula p = g.some(), q = h.some(), r = i.some(), tt = g.eq(g), ff = g.eq(g).not();
	
	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);

	private Formula v1;
	private SATFactory v2;
	private boolean v3;
	
	public TemporalIdentitiesTests(Formula v1, SATFactory v2, boolean v3) {
		this.v1 = v1;
		this.v2 = v2;
		this.v3 = v3;
	}

	@Parameters(name = "{0} {1} {2}")
	public static Collection<Object[]> data() {
		Object[][] data = new Object[][] {
			{(p.after().always()).iff(p.always().after()), 																	SATFactory.Glucose,					false}, // t81
			{(p.always()).iff(p.not().eventually().not()), 																	SATFactory.Glucose,					false}, // t83
			{(ff.after()).iff(ff), 																							SATFactory.Glucose,					false}, // t85
			{(ff.eventually()).iff(ff), 																					SATFactory.Glucose,					false}, // t87
			{((p.after().until(q)).and(r)).iff(((p.after()).until(q)).and(r)),												SATFactory.Glucose,					false}, // t89
			{(tt.after()).iff(tt), 																							SATFactory.Glucose,					false}, // t91
			{(ff.always()).iff(ff), 																						SATFactory.Glucose,					false}, // t92
			{(tt.eventually()).iff(tt), 																					SATFactory.Glucose,					false}, // t94
			{(ff.eventually().eventually()).iff(ff.eventually()),															SATFactory.Glucose,					false}, // t95
			{(tt.always()).iff(tt), 																						SATFactory.Glucose,					false}, // t97
			{(ff.always().always()).iff(ff.always()), 																		SATFactory.Glucose,					false}, // t98
			{(p.until(tt)).iff(tt), 																						SATFactory.Glucose,					false}, // t100
			{(ff.until(p)).iff(p), 																							SATFactory.Glucose,					false}, // t101
			{(p.until(ff)).iff(ff), 																						SATFactory.Glucose,					false}, // t102
			{(p.until(p)).iff(p), 																							SATFactory.Glucose,					false}, // t103
			{(tt.until(p)).iff(p.eventually()), 																			SATFactory.Glucose,					false}, // t104
			{((p.after()).until(q.after())).iff((p.until(q)).after()), 														SATFactory.Glucose,					false}, // t105
			{(p.releases(q)).iff(((p.not()).until(q.not())).not()), 														SATFactory.Glucose,					false}, // t107
			{(p.releases(tt)).iff(tt), 																						SATFactory.Glucose,					false}, // t108
			{(p.releases(ff)).iff(ff), 																						SATFactory.Glucose,					false}, // t109
			{(tt.releases(p).iff(p)), 																						SATFactory.Glucose,					false}, // t110
			{(p.releases(p).iff(p)), 																						SATFactory.Glucose,					false}, // t111
			{(ff.releases(p).iff(p.always())), 																				SATFactory.Glucose,					false}, // t112
			{(p.releases(q)).iff(q.and(p.or((p.releases(q)).after()))), 													SATFactory.Glucose,					false}, // t113
			{(p.always().eventually().after()).iff(p.always().eventually()), 												SATFactory.Glucose,					false}, // t115
			{(p.eventually().always().after()).iff(p.eventually().always()), 												SATFactory.Glucose,					false}, // t116
			{(p.eventually().after()).iff(p.after().eventually()), 															SATFactory.Glucose,					false}, // t117
			{((p.until(q)).eventually()).iff(q.eventually()), 																SATFactory.Glucose,					false}, // t119
			{((p.and(q.after())).always().eventually()).iff((p.and(q)).always().eventually()), 								SATFactory.Glucose,					false}, // t120
			{((p.and(q.always())).always().eventually()).iff((p.and(q)).always().eventually()), 							SATFactory.Glucose,					false}, // t121
			{((p.or(q.always())).always().eventually()).iff((p.always().or(q.always())).eventually()), 						SATFactory.Glucose,					false}, // t122
			{((p.and(q.eventually())).always().eventually()).iff((p.always().eventually()).and(q.eventually().always())),	SATFactory.Glucose,					false}, // t123
			{((p.or(q.eventually())).always().eventually()).iff((p.always().eventually()).or(q.eventually().always())),		SATFactory.Glucose,					false}, // t124
			{((p.or(q.after())).eventually().always()).iff((p.or(q)).eventually().always()),								SATFactory.Glucose,					false}, // t126
			{((p.or(q.eventually())).eventually().always()).iff((p.or(q)).eventually().always()),							SATFactory.Glucose,					false}, // t127
			{((p.and(q.eventually())).eventually().always()).iff(((p.eventually()).and(q.eventually())).always()),			SATFactory.Glucose,					false}, // t128
			{((p.and(q.always())).eventually().always()).iff((p.eventually().always()).and(q.always().eventually())),		SATFactory.Glucose,					false}, // t129
			{((p.or(q.always())).eventually().always()).iff((p.eventually().always()).or(q.always().eventually())),			SATFactory.Glucose,					false}, // t130
			{(p.until(p.always())).iff(p.always()),																			SATFactory.Glucose,					false}, // t132
			{(p.releases(p.eventually())).iff(p.eventually()),																SATFactory.Glucose,					false}, // t133	
			{((p.always().eventually()).and(q.always().eventually())).iff((p.and(q)).always().eventually()),				SATFactory.Glucose,					false}, // t136
			{((p.after()).and(q.after())).iff((p.and(q)).after()),															SATFactory.Glucose,					false}, // t137
			{((p.after()).and(q.always().eventually())).iff((p.and(q.always().eventually())).after()),						SATFactory.Glucose,					false}, // t138
			{((p.until(q)).and(r.until(q))).iff((p.and(r)).until(q)),														SATFactory.Glucose,					false}, // t139
			{((p.releases(q)).and(p.releases(r))).iff(p.releases(q.and(r))),												SATFactory.Glucose,					false}, // t140
			{((p.until(q)).or(p.until(r))).iff(p.until(q.or(r))),															SATFactory.Glucose,					false}, // t141
			{((p.releases(q)).or(r.releases(q))).iff((p.or(r)).releases(q)),												SATFactory.Glucose,					false}, // t142
			{((q.always()).or(p.releases(q))).iff(p.releases(q)),															SATFactory.Glucose,					false}, // t144
			{((p.after()).releases(q.after())).iff((p.releases(q)).after()),												SATFactory.Glucose,					false}, // t147
			{((p.releases(q)).always()).iff(q.always()),																	SATFactory.Glucose,					false}, // t149
			{(p.once().always().eventually()).iff(p.eventually()),															SATFactory.Glucose,					false}, // t151
			{((p.and(q.since(r))).eventually()).iff((r.and(p.or((q.until(q.and(p))).after()))).eventually()),				SATFactory.Glucose,					false}, // t153
			{(p.after().always()).iff(p.always().after()), 																	SATFactory.electrod("-t","nuXmv"),	false}, // t81
			{(p.always()).iff(p.not().eventually().not()), 																	SATFactory.electrod("-t","nuXmv"),	false}, // t83
			{(ff.after()).iff(ff), 																							SATFactory.electrod("-t","nuXmv"),	false}, // t85
			{(ff.eventually()).iff(ff), 																					SATFactory.electrod("-t","nuXmv"),	false}, // t87
			{((p.after().until(q)).and(r)).iff(((p.after()).until(q)).and(r)),												SATFactory.electrod("-t","nuXmv"),	false}, // t89
			{(tt.after()).iff(tt), 																							SATFactory.electrod("-t","nuXmv"),	false}, // t91
			{(ff.always()).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t92
			{(tt.eventually()).iff(tt), 																					SATFactory.electrod("-t","nuXmv"),	false}, // t94
			{(ff.eventually().eventually()).iff(ff.eventually()),															SATFactory.electrod("-t","nuXmv"),	false}, // t95
			{(tt.always()).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t97
			{(ff.always().always()).iff(ff.always()), 																		SATFactory.electrod("-t","nuXmv"),	false}, // t98
			{(p.until(tt)).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t100
			{(ff.until(p)).iff(p), 																							SATFactory.electrod("-t","nuXmv"),	false}, // t101
			{(p.until(ff)).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t102
			{(p.until(p)).iff(p), 																							SATFactory.electrod("-t","nuXmv"),	false}, // t103
			{(tt.until(p)).iff(p.eventually()), 																			SATFactory.electrod("-t","nuXmv"),	false}, // t104
			{((p.after()).until(q.after())).iff((p.until(q)).after()), 														SATFactory.electrod("-t","nuXmv"),	false}, // t105
			{(p.releases(q)).iff(((p.not()).until(q.not())).not()), 														SATFactory.electrod("-t","nuXmv"),	false}, // t107
			{(p.releases(tt)).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t108
			{(p.releases(ff)).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t109
			{(tt.releases(p).iff(p)), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t110
			{(p.releases(p).iff(p)), 																						SATFactory.electrod("-t","nuXmv"),	false}, // t111
			{(ff.releases(p).iff(p.always())), 																				SATFactory.electrod("-t","nuXmv"),	false}, // t112
			{(p.releases(q)).iff(q.and(p.or((p.releases(q)).after()))), 													SATFactory.electrod("-t","nuXmv"),	false}, // t113
			{(p.always().eventually().after()).iff(p.always().eventually()), 												SATFactory.electrod("-t","nuXmv"),	false}, // t115
			{(p.eventually().always().after()).iff(p.eventually().always()), 												SATFactory.electrod("-t","nuXmv"),	false}, // t116
			{(p.eventually().after()).iff(p.after().eventually()), 															SATFactory.electrod("-t","nuXmv"),	false}, // t117
			{((p.until(q)).eventually()).iff(q.eventually()), 																SATFactory.electrod("-t","nuXmv"),	false}, // t119
			{((p.and(q.after())).always().eventually()).iff((p.and(q)).always().eventually()), 								SATFactory.electrod("-t","nuXmv"),	false}, // t120
			{((p.and(q.always())).always().eventually()).iff((p.and(q)).always().eventually()), 							SATFactory.electrod("-t","nuXmv"),	false}, // t121
			{((p.or(q.always())).always().eventually()).iff((p.always().or(q.always())).eventually()), 						SATFactory.electrod("-t","nuXmv"),	false}, // t122
			{((p.and(q.eventually())).always().eventually()).iff((p.always().eventually()).and(q.eventually().always())),	SATFactory.electrod("-t","nuXmv"),	false}, // t123
			{((p.or(q.eventually())).always().eventually()).iff((p.always().eventually()).or(q.eventually().always())),		SATFactory.electrod("-t","nuXmv"),	false}, // t124
			{((p.or(q.after())).eventually().always()).iff((p.or(q)).eventually().always()),								SATFactory.electrod("-t","nuXmv"),	false}, // t126
			{((p.or(q.eventually())).eventually().always()).iff((p.or(q)).eventually().always()),							SATFactory.electrod("-t","nuXmv"),	false}, // t127
			{((p.and(q.eventually())).eventually().always()).iff(((p.eventually()).and(q.eventually())).always()),			SATFactory.electrod("-t","nuXmv"),	false}, // t128
			{((p.and(q.always())).eventually().always()).iff((p.eventually().always()).and(q.always().eventually())),		SATFactory.electrod("-t","nuXmv"),	false}, // t129
			{((p.or(q.always())).eventually().always()).iff((p.eventually().always()).or(q.always().eventually())),			SATFactory.electrod("-t","nuXmv"),	false}, // t130
			{(p.until(p.always())).iff(p.always()),																			SATFactory.electrod("-t","nuXmv"),	false}, // t132
			{(p.releases(p.eventually())).iff(p.eventually()),																SATFactory.electrod("-t","nuXmv"),	false}, // t133	
			{((p.always().eventually()).and(q.always().eventually())).iff((p.and(q)).always().eventually()),				SATFactory.electrod("-t","nuXmv"),	false}, // t136
			{((p.after()).and(q.after())).iff((p.and(q)).after()),															SATFactory.electrod("-t","nuXmv"),	false}, // t137
			{((p.after()).and(q.always().eventually())).iff((p.and(q.always().eventually())).after()),						SATFactory.electrod("-t","nuXmv"),	false}, // t138
			{((p.until(q)).and(r.until(q))).iff((p.and(r)).until(q)),														SATFactory.electrod("-t","nuXmv"),	false}, // t139
			{((p.releases(q)).and(p.releases(r))).iff(p.releases(q.and(r))),												SATFactory.electrod("-t","nuXmv"),	false}, // t140
			{((p.until(q)).or(p.until(r))).iff(p.until(q.or(r))),															SATFactory.electrod("-t","nuXmv"),	false}, // t141
			{((p.releases(q)).or(r.releases(q))).iff((p.or(r)).releases(q)),												SATFactory.electrod("-t","nuXmv"),	false}, // t142
			{((q.always()).or(p.releases(q))).iff(p.releases(q)),															SATFactory.electrod("-t","nuXmv"),	false}, // t144
			{((p.after()).releases(q.after())).iff((p.releases(q)).after()),												SATFactory.electrod("-t","nuXmv"),	false}, // t147
			{((p.releases(q)).always()).iff(q.always()),																	SATFactory.electrod("-t","nuXmv"),	false}, // t149
			{(p.once().always().eventually()).iff(p.eventually()),															SATFactory.electrod("-t","nuXmv"),	false}, // t151
			{((p.and(q.since(r))).eventually()).iff((r.and(p.or((q.until(q.and(p))).after()))).eventually()),				SATFactory.electrod("-t","nuXmv"),	false}, // t153
			{(p.after().always()).iff(p.always().after()), 																	SATFactory.electrod("-t","nuXmv"),	true}, // t81
			{(p.always()).iff(p.not().eventually().not()), 																	SATFactory.electrod("-t","nuXmv"),	true}, // t83
			{(ff.after()).iff(ff), 																							SATFactory.electrod("-t","nuXmv"),	true}, // t85
			{(ff.eventually()).iff(ff), 																					SATFactory.electrod("-t","nuXmv"),	true}, // t87
			{((p.after().until(q)).and(r)).iff(((p.after()).until(q)).and(r)),												SATFactory.electrod("-t","nuXmv"),	true}, // t89
			{(tt.after()).iff(tt), 																							SATFactory.electrod("-t","nuXmv"),	true}, // t91
			{(ff.always()).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t92
			{(tt.eventually()).iff(tt), 																					SATFactory.electrod("-t","nuXmv"),	true}, // t94
			{(ff.eventually().eventually()).iff(ff.eventually()),															SATFactory.electrod("-t","nuXmv"),	true}, // t95
			{(tt.always()).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t97
			{(ff.always().always()).iff(ff.always()), 																		SATFactory.electrod("-t","nuXmv"),	true}, // t98
			{(p.until(tt)).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t100
			{(ff.until(p)).iff(p), 																							SATFactory.electrod("-t","nuXmv"),	true}, // t101
			{(p.until(ff)).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t102
			{(p.until(p)).iff(p), 																							SATFactory.electrod("-t","nuXmv"),	true}, // t103
			{(tt.until(p)).iff(p.eventually()), 																			SATFactory.electrod("-t","nuXmv"),	true}, // t104
			{((p.after()).until(q.after())).iff((p.until(q)).after()), 														SATFactory.electrod("-t","nuXmv"),	true}, // t105
			{(p.releases(q)).iff(((p.not()).until(q.not())).not()), 														SATFactory.electrod("-t","nuXmv"),	true}, // t107
			{(p.releases(tt)).iff(tt), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t108
			{(p.releases(ff)).iff(ff), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t109
			{(tt.releases(p).iff(p)), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t110
			{(p.releases(p).iff(p)), 																						SATFactory.electrod("-t","nuXmv"),	true}, // t111
			{(ff.releases(p).iff(p.always())), 																				SATFactory.electrod("-t","nuXmv"),	true}, // t112
			{(p.releases(q)).iff(q.and(p.or((p.releases(q)).after()))), 													SATFactory.electrod("-t","nuXmv"),	true}, // t113
			{(p.always().eventually().after()).iff(p.always().eventually()), 												SATFactory.electrod("-t","nuXmv"),	true}, // t115
			{(p.eventually().always().after()).iff(p.eventually().always()), 												SATFactory.electrod("-t","nuXmv"),	true}, // t116
			{(p.eventually().after()).iff(p.after().eventually()), 															SATFactory.electrod("-t","nuXmv"),	true}, // t117
			{((p.until(q)).eventually()).iff(q.eventually()), 																SATFactory.electrod("-t","nuXmv"),	true}, // t119
			{((p.and(q.after())).always().eventually()).iff((p.and(q)).always().eventually()), 								SATFactory.electrod("-t","nuXmv"),	true}, // t120
			{((p.and(q.always())).always().eventually()).iff((p.and(q)).always().eventually()), 							SATFactory.electrod("-t","nuXmv"),	true}, // t121
			{((p.or(q.always())).always().eventually()).iff((p.always().or(q.always())).eventually()), 						SATFactory.electrod("-t","nuXmv"),	true}, // t122
			{((p.and(q.eventually())).always().eventually()).iff((p.always().eventually()).and(q.eventually().always())),	SATFactory.electrod("-t","nuXmv"),	true}, // t123
			{((p.or(q.eventually())).always().eventually()).iff((p.always().eventually()).or(q.eventually().always())),		SATFactory.electrod("-t","nuXmv"),	true}, // t124
			{((p.or(q.after())).eventually().always()).iff((p.or(q)).eventually().always()),								SATFactory.electrod("-t","nuXmv"),	true}, // t126
			{((p.or(q.eventually())).eventually().always()).iff((p.or(q)).eventually().always()),							SATFactory.electrod("-t","nuXmv"),	true}, // t127
			{((p.and(q.eventually())).eventually().always()).iff(((p.eventually()).and(q.eventually())).always()),			SATFactory.electrod("-t","nuXmv"),	true}, // t128
			{((p.and(q.always())).eventually().always()).iff((p.eventually().always()).and(q.always().eventually())),		SATFactory.electrod("-t","nuXmv"),	true}, // t129
			{((p.or(q.always())).eventually().always()).iff((p.eventually().always()).or(q.always().eventually())),			SATFactory.electrod("-t","nuXmv"),	true}, // t130
			{(p.until(p.always())).iff(p.always()),																			SATFactory.electrod("-t","nuXmv"),	true}, // t132
			{(p.releases(p.eventually())).iff(p.eventually()),																SATFactory.electrod("-t","nuXmv"),	true}, // t133	
			{((p.always().eventually()).and(q.always().eventually())).iff((p.and(q)).always().eventually()),				SATFactory.electrod("-t","nuXmv"),	true}, // t136
			{((p.after()).and(q.after())).iff((p.and(q)).after()),															SATFactory.electrod("-t","nuXmv"),	true}, // t137
			{((p.after()).and(q.always().eventually())).iff((p.and(q.always().eventually())).after()),						SATFactory.electrod("-t","nuXmv"),	true}, // t138
			{((p.until(q)).and(r.until(q))).iff((p.and(r)).until(q)),														SATFactory.electrod("-t","nuXmv"),	true}, // t139
			{((p.releases(q)).and(p.releases(r))).iff(p.releases(q.and(r))),												SATFactory.electrod("-t","nuXmv"),	true}, // t140
			{((p.until(q)).or(p.until(r))).iff(p.until(q.or(r))),															SATFactory.electrod("-t","nuXmv"),	true}, // t141
			{((p.releases(q)).or(r.releases(q))).iff((p.or(r)).releases(q)),												SATFactory.electrod("-t","nuXmv"),	true}, // t142
			{((q.always()).or(p.releases(q))).iff(p.releases(q)),															SATFactory.electrod("-t","nuXmv"),	true}, // t144
			{((p.after()).releases(q.after())).iff((p.releases(q)).after()),												SATFactory.electrod("-t","nuXmv"),	true}, // t147
			{((p.releases(q)).always()).iff(q.always()),																	SATFactory.electrod("-t","nuXmv"),	true}, // t149
			{(p.once().always().eventually()).iff(p.eventually()),															SATFactory.electrod("-t","nuXmv"),	true}, // t151
			{((p.and(q.since(r))).eventually()).iff((r.and(p.or((q.until(q.and(p))).after()))).eventually()),				SATFactory.electrod("-t","nuXmv"),	true}, // t153
		};
		return Arrays.asList(data);
	}
	
	@Test
	public void test() {
		int n = 3;
		
		final List<String> atoms = new ArrayList<String>(n);

		for (int i = 0; i <= n; i++)
			atoms.add("n" + i);

		Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		b.bound(g, f.range(f.tuple("n0"), f.tuple("n"+n)));
		b.bound(h, f.range(f.tuple("n0"), f.tuple("n"+n)));
		b.bound(i, f.range(f.tuple("n0"), f.tuple("n"+n)));
		
		opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(v2);
		opt.setRunUnbounded(v3);
		dsolver = new PardinusSolver(opt);
		Solution sol = dsolver.solve(v1.not(), b);
		
		assertFalse(sol.sat());

	}

}
