package il.ac.bgu.cs.formalmethodsintro.base.sanity;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;

import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.GraphvizPainter;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.Test;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

/**
 *
 * Sanity test for the provided {@link ProgramGraph}.
 *
 * @author michael
 */
public class ProgramGraphSanityTest {

    @Test
    public void consistencyChecks() {
        ProgramGraph<String, String> sut = FvmFacade.get().createProgramGraph();
        sut.addTransition(new PGTransition<>("from", "true", "act", "to"));
        assertEquals(Set.of("from", "to"), sut.getLocations());

        sut.setInitial("newLocation", true);
        assertEquals(Set.of("from", "to", "newLocation"), sut.getLocations());
        assertEquals(Set.of("newLocation"), sut.getInitialLocations());

        sut.setInitial("from", true);
        assertEquals(Set.of("from", "newLocation"), sut.getInitialLocations());

        sut.setInitial("newLocation", false);
        assertEquals(Set.of("from"), sut.getInitialLocations());
    }

    @Test
    public void testEqualities() {
        ProgramGraph<String, String> sut1 = FvmFacade.get().createProgramGraph();
        ProgramGraph<String, String> sut2 = FvmFacade.get().createProgramGraph();

        assertEquals(sut1, sut2);

        sut1.setName("sut1");
        //assertNotEquals(sut1, sut2);

        sut1.setName(null);

        sut1.addTransition(new PGTransition<>("from", "true", "act", "to"));
        sut2.addTransition(new PGTransition<>("from", "true", "act", "to"));
        sut1.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        sut2.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        assertEquals(sut1, sut2);

        sut2.addTransition(new PGTransition<>("fromA", "true", "act", "toA"));
        assertEquals(sut1, sut2);

        sut2.addTransition(new PGTransition<>("fromA", "true", "actX", "toA"));
        assertNotEquals(sut1, sut2);
    }

    @Test
    public void testCs() {
        TransitionSystem<Pair<List<Integer>,Map<String,Object>>, String, String> ts = fvmFacadeImpl.transitionSystemFromChannelSystem(build());
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
    }

    public static ChannelSystem<Integer, String> build() {
        List<ProgramGraph<Integer, String>> pgs = new LinkedList<>();

        pgs.add(build1());
        pgs.add(build2());
        pgs.add(build3());

        return new ChannelSystem<>(pgs);
    }

    private static FvmFacade fvmFacadeImpl = FvmFacade.get();
    private static ProgramGraph<Integer, String> build1() {
        ProgramGraph<Integer, String> pg = fvmFacadeImpl.createProgramGraph();
        
        pg.setInitial(1, true);

        pg.addTransition(new PGTransition<>(1, "", "_req!1", 2));
        pg.addTransition(new PGTransition<>(2, "", "_rep?ans1", 3));

        return pg;
    }
    private static ProgramGraph<Integer, String> build2() {
        ProgramGraph<Integer, String> pg = fvmFacadeImpl.createProgramGraph();
        
        pg.setInitial(1, true);
        //pg.addInitalization(asList("ans2:=0", "req:=[]"));
        pg.addTransition(new PGTransition<>(1, "", "_req!2", 2));
        pg.addTransition(new PGTransition<>(2, "", "_rep?ans2", 3));

        return pg;
    }
    private static ProgramGraph<Integer, String> build3() {
        ProgramGraph<Integer, String> pg = fvmFacadeImpl.createProgramGraph();
        
        pg.setInitial(1, true);

        pg.addTransition(new PGTransition<>(1, "", "_req?msg", 2));
        pg.addTransition(new PGTransition<>(2, "", "_rep!msg", 1));

        return pg;
    }
}
