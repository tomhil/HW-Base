package il.ac.bgu.cs.formalmethodsintro.base;

import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

public class FvmFacadeTest {


    FvmFacade fvmFacade;
    TransitionSystem simple;

    @Before
    public void setUp() throws Exception {
        fvmFacade=new FvmFacade();
        simple=buildSimpleTS();
    }

    private TransitionSystem buildSimpleTS() {
        TransitionSystem ts=new TransitionSystem();
        ts.addInitialState(1);
        ts.addAllStates(new Integer[]{2,3,4,5});
        ts.addAllActions(new Character[]{'a','b','c'});


        ts.addTransition(new TSTransition(1,'a',2));
        ts.addTransition(new TSTransition(1,'b',3));
        ts.addTransition(new TSTransition(3,'c',4));
        ts.addTransition(new TSTransition(2,'a',2));

        ts.addAllAtomicPropositions(new String[]{"x","y","z"});


        ts.addToLabel(1,"x");
        ts.addToLabel(2,"y");
        ts.addToLabel(3,"z");

        return ts;
    }

    @After
    public void tearDown() throws Exception {
    }


    @Test
    public void get() {
    }

    @Test
    public void isActionDeterministic() {
    }

    @Test
    public void isAPDeterministic() {
    }

    @Test
    public void isExecution() {
    }

    @Test
    public void isExecutionFragment() {
    }

    @Test
    public void isInitialExecutionFragment() {
    }

    @Test
    public void isMaximalExecutionFragment() {
    }

    @Test
    public void isStateTerminal() {
    }

    @Test
    public void TEstPost_AllPostState_WithoutAction() {
        try{
            fvmFacade.post(simple,6);
            Assert.assertTrue(false);
        }catch (StateNotFoundException s){
            Set<Integer> posts=fvmFacade.post(simple,1);
            Assert.assertTrue(posts.contains(2) && posts.contains(3) && posts.size()==2);
            posts=fvmFacade.post(simple,2);
            Assert.assertTrue(posts.contains(2) &&  posts.size()==1);
            posts=fvmFacade.post(simple,5);
            Assert.assertTrue(posts.size()==0);
        }
    }

    @Test
    public void testPost_forGroupOfStates() {
        Set<Integer> c1 = new HashSet<>(Arrays.asList(1, 3));
        Set<Integer> c2 = new HashSet<>(Arrays.asList(5));
        Set<Integer> c3 = new HashSet<>(Arrays.asList(6));

        try{
            fvmFacade.post((TransitionSystem<Integer, ?, ?>) simple, c3);
            Assert.assertTrue("testPost_forGroupOfStates: State not contain in TS",false);
        }catch (StateNotFoundException s){
            Set<Integer> posts= fvmFacade.post((TransitionSystem<Integer, ?, ?>) simple, c1);
            Assert.assertTrue("testPost_forGroupOfStates: regular case fail",posts.contains(2) && posts.contains(3)&& posts.contains(4) && posts.size()==3);
           posts= fvmFacade.post((TransitionSystem<Integer, ?, ?>) simple, c2);
            Assert.assertTrue("testPost_forGroupOfStates: empty case fail",posts.size()==0);
        }
    }

    @Test
    public void testPost_withSingleActionAndSingleState() {
        try{
            fvmFacade.post(simple,6,'a');
            Assert.assertTrue(false);
        }catch (StateNotFoundException s){
            Set<Integer> posts=fvmFacade.post(simple,1, 'a');
            Assert.assertTrue(posts.contains(2) && !posts.contains(3) && posts.size()==1);
            posts=fvmFacade.post(simple,2,'a');
            Assert.assertTrue(posts.contains(2) &&  posts.size()==1);
            posts=fvmFacade.post(simple,5,'a');
            Assert.assertTrue(posts.size()==0);
        }
    }

    @Test
    public void testPost_withSingleActionAndGroupState() {
        Set<Integer> c1 = new HashSet<>(Arrays.asList(1, 3));
        Set<Integer> c2 = new HashSet<>(Arrays.asList(5));
        Set<Integer> c3 = new HashSet<>(Arrays.asList(6));

        try{
            fvmFacade.post((TransitionSystem<Integer, Character, ?>) simple, c3,'a');
            Assert.assertTrue("testPost_forGroupOfStates: State not contain in TS",false);
        }catch (StateNotFoundException s){
            Set<Integer> posts= fvmFacade.post((TransitionSystem<Integer, Character, ?>) simple, c1,'a');
            Assert.assertTrue("testPost_forGroupOfStates: regular case fail",posts.contains(2) && posts.size()==1);
            posts= fvmFacade.post((TransitionSystem<Integer, Character, ?>) simple, c2,'a');
            Assert.assertTrue("testPost_forGroupOfStates: empty case fail",posts.size()==0);
        }
    }

    @Test
    public void preAllState_WithoutAction() {
        try {
            fvmFacade.pre(simple, 6);
            Assert.assertTrue(false);
        } catch (StateNotFoundException s) {
            Set<Integer> pres = fvmFacade.pre(simple, 1);
            Assert.assertTrue(pres.size() == 0);
            pres = fvmFacade.pre(simple, 2);
            Assert.assertTrue(pres.contains(2) && pres.contains(1) && pres.size() == 2);
            pres = fvmFacade.pre(simple, 5);
            Assert.assertTrue(pres.size() == 0);
        }
    }

    @Test
    public void testPreforGroupOfStates() {
        Set<Integer> c1 = new HashSet<>(Arrays.asList(1, 3));
        Set<Integer> c2 = new HashSet<>(Arrays.asList(5));
        Set<Integer> c3 = new HashSet<>(Arrays.asList(6));

        try{
            fvmFacade.pre((TransitionSystem<Integer, ?, ?>) simple, c3);
            Assert.assertTrue("testPreforGroupOfStates: State not contain in TS",false);
        }catch (StateNotFoundException s){
            Set<Integer> pres= fvmFacade.pre((TransitionSystem<Integer, ?, ?>) simple, c1);
            Assert.assertTrue("testPreforGroupOfStates: regular case fail",pres.contains(1) && pres.size()==1);
            pres= fvmFacade.pre((TransitionSystem<Integer, ?, ?>) simple, c2);
            Assert.assertTrue("testPreforGroupOfStates: empty case fail",pres.size()==0);
        }
    }


    @Test
    public void testPre__withSingleActionAndSingleState() {
        try{
            fvmFacade.pre(simple,6,'a');
            Assert.assertTrue(false);
        }catch (StateNotFoundException s){
            Set<Integer> pres=fvmFacade.pre(simple,1, 'a');
            Assert.assertTrue( pres.size()==0);
            pres=fvmFacade.pre(simple,2,'a');
            Assert.assertTrue(pres.contains(2) && pres.contains(1) &&  pres.size()==2);
            pres=fvmFacade.pre(simple,5,'a');
            Assert.assertTrue(pres.size()==0);
        }
    }

    @Test
    public void testPre_withSingleActionAndGroupState() {
        Set<Integer> c1 = new HashSet<>(Arrays.asList(1, 3));
        Set<Integer> c2 = new HashSet<>(Arrays.asList(5));
        Set<Integer> c3 = new HashSet<>(Arrays.asList(6));

        try{
            fvmFacade.pre((TransitionSystem<Integer, Character, ?>) simple, c3,'a');
            Assert.assertTrue("testPre_withSingleActionAndGroupState: State not contain in TS",false);
        }catch (StateNotFoundException s){
            Set<Integer> pres= fvmFacade.pre((TransitionSystem<Integer, Character, ?>) simple, c1,'b');
            Assert.assertTrue("testPre_withSingleActionAndGroupState: regular case fail",pres.contains(1) && pres.size()==1);
            pres= fvmFacade.pre((TransitionSystem<Integer, Character, ?>) simple, c2,'a');
            Assert.assertTrue("testPre_withSingleActionAndGroupState: empty case fail",pres.size()==0);
        }
    }

    @Test
    public void reach() {
    }

    @Test
    public void interleave() {
    }

    @Test
    public void testInterleave() {
    }

    @Test
    public void createProgramGraph() {
    }

    @Test
    public void testInterleave1() {
    }

    @Test
    public void transitionSystemFromCircuit() {
    }

    @Test
    public void transitionSystemFromProgramGraph() {
    }

    @Test
    public void transitionSystemFromChannelSystem() {
    }

    @Test
    public void testTransitionSystemFromChannelSystem() {
    }

    @Test
    public void programGraphFromNanoPromela() {
    }

    @Test
    public void programGraphFromNanoPromelaString() {
    }

    @Test
    public void testProgramGraphFromNanoPromela() {
    }

    @Test
    public void product() {
    }

    @Test
    public void verifyAnOmegaRegularProperty() {
    }

    @Test
    public void LTL2NBA() {
    }

    @Test
    public void GNBA2NBA() {
    }
}