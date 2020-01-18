package il.ac.bgu.cs.formalmethodsintro.base;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;

public class TransitionsCheck {
	//ap-d ap-p
	public TransitionSystem<String, String, String> getTs1() {
		TransitionSystem<String, String, String> ts1 = new TransitionSystem<>();
		
		ts1.setName("ts1");
		ts1.addStates("1", "2", "3", "4", "5", "6");
		ts1.addActions("a1", "a2");
		ts1.addAtomicPropositions("p1", "p2");
		ts1.addInitialState("1");
		ts1.addToLabel("1", "p1");
		ts1.addToLabel("2", "p1");
		ts1.addToLabel("3", "p1");
		ts1.addToLabel("3", "p2");
		ts1.addToLabel("4", "p1");
		ts1.addToLabel("5", "p2");
		ts1.addTransition(new TSTransition<String, String>("1", "a1", "2"));
		ts1.addTransition(new TSTransition<String, String>("1", "a2", "3"));
		ts1.addTransition(new TSTransition<String, String>("2", "a1", "4"));
		ts1.addTransition(new TSTransition<String, String>("3", "a1", "4"));
		ts1.addTransition(new TSTransition<String, String>("4", "a1", "1"));
		ts1.addTransition(new TSTransition<String, String>("4", "a2", "5"));
		ts1.addTransition(new TSTransition<String, String>("6", "a2", "2"));
		
		return ts1;
	}
	
	//ap-d nap-p
	public TransitionSystem<String, String, String> getTs2() {
		TransitionSystem<String, String, String> ts2 = getTs1();
		ts2.setName("ts2");
		ts2.removeLabel("5", "p2");
		ts2.addToLabel("5", "p1");
		return ts2;
	}
		
	
	//nap-d 2 inits nap-p
	public TransitionSystem<String, String, String> getTs3() {
		TransitionSystem<String, String, String> ts3 = getTs1();
		ts3.setName("ts3");
		ts3.addInitialState("2");
		return ts3;
	}

	//nap-d ap-p
	public TransitionSystem<String, String, String> getTs4() {
		TransitionSystem<String, String, String> ts4 = getTs1();
		ts4.setName("ts4");
		ts4.removeTransition(new TSTransition<String, String>("4", "a1", "1"));
		ts4.addTransition(new TSTransition<String, String>("4", "a2", "1"));
		return ts4;
	}
	
	public TransitionSystem<String, String, String> getTsShort() {
		TransitionSystem<String, String, String> tsShort = new TransitionSystem<>();
		
		tsShort.setName("tsShort");
		tsShort.addStates("1", "2");
		tsShort.addActions("a1", "a2");
		tsShort.addAtomicPropositions("p1", "p2");
		tsShort.addInitialState("1");
		tsShort.addToLabel("1", "p1");
		tsShort.addToLabel("2", "p1");
		tsShort.addToLabel("2", "p2");
		tsShort.addTransition(new TSTransition<String, String>("1", "a1", "2"));
		tsShort.addTransition(new TSTransition<String, String>("2", "a2", "1"));		
		return tsShort;
	}
	
	FvmFacade f = FvmFacade.get();
    @Test
    public void featuresCheck() {
		TransitionSystem<String, String, String> ts1 = getTs1();
		TransitionSystem<String, String, String> ts2 = getTs2();
		TransitionSystem<String, String, String> ts3 = getTs3();
		TransitionSystem<String, String, String> ts4 = getTs4();
		assertTrue(f.isActionDeterministic(ts1));
		assertTrue(f.isAPDeterministic(ts1));
		assertTrue(f.isActionDeterministic(ts2));
		assertFalse(f.isAPDeterministic(ts2));
		assertFalse(f.isActionDeterministic(ts3));
		assertFalse(f.isAPDeterministic(ts3));
		assertFalse(f.isActionDeterministic(ts4));
		assertTrue(f.isAPDeterministic(ts4));
		
		assertFalse(f.isStateTerminal(ts1, "4"));
		assertTrue(f.isStateTerminal(ts1, "5"));
		Set<String> s1 = new HashSet<String>();
		s1.add("1");		s1.add("5");
		assertEquals(f.post(ts1, "4"), s1);
		Set<String> s2 = new HashSet<String>();
		s2.add("2");		s2.add("3");
		assertEquals(f.pre(ts1, "4"), s2);
		
		Set<String> s3 = new HashSet<String>();
		s3.add("1");s3.add("2");s3.add("3");s3.add("4");s3.add("5");
		assertEquals(f.reach(ts1), s3);		
    }    

    @Test
    public void execution() {
		TransitionSystem<String, String, String> ts1 = getTs1();
		assertTrue(f.isExecution(ts1, AlternatingSequence.of("1", "a2", "3", "a1", "4", "a2", "5")));
		assertFalse(f.isExecution(ts1, AlternatingSequence.of("1", "a2", "3", "a1", "4")));
		assertFalse(f.isExecution(ts1, AlternatingSequence.of("3", "a1", "4", "a2", "5")));
		assertFalse(f.isExecution(ts1, AlternatingSequence.of("3", "a1", "4")));
		
		assertTrue(f.isExecutionFragment(ts1, AlternatingSequence.of("1", "a2", "3", "a1", "4")));
		assertTrue(f.isExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4", "a2", "5")));
		assertTrue(f.isExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4")));
		assertFalse(f.isExecutionFragment(ts1, AlternatingSequence.of("3", "a2", "4", "a2", "5")));
		
		assertTrue(f.isInitialExecutionFragment(ts1, AlternatingSequence.of("1", "a2", "3", "a1", "4")));
		assertFalse(f.isInitialExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4", "a2", "5")));
		assertFalse(f.isInitialExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4")));
		
		assertFalse(f.isMaximalExecutionFragment(ts1, AlternatingSequence.of("1", "a2", "3", "a1", "4")));
		assertTrue(f.isMaximalExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4", "a2", "5")));
		assertFalse(f.isMaximalExecutionFragment(ts1, AlternatingSequence.of("3", "a1", "4")));
    }
    
    public static void printTS(TransitionSystem<?, ?, ?> ts){
    	System.out.println(ts);
    	System.out.print("<");
    	for(Object s : ts.getStates())
        	System.out.print(s.toString() + " ");
    	System.out.println(">");
    	
    	System.out.print("<");
    	for(TSTransition<?, ?> t : ts.getTransitions())
        	System.out.print(t.getFrom() + " " + t.getAction() + " " + t.getTo() + ";");
    	System.out.println(">");
    	
    	System.out.print("<");
    	 Map<?, ?> a = ts.getLabelingFunction();
    	for(Entry<?, ?> s : a.entrySet()) {
        	System.out.print(s.getKey() + " [");
        	for(Object p : ((Set<?>) s.getValue()))
        		System.out.print(p + " ");
        	System.out.print("] ");
    	}
    	System.out.println(">");
		System.out.println("");
		//System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
    }
    @Test
    public void interleave() {
    	TransitionSystem<String, String, String> tsshort = getTsShort();
    	printTS(tsshort);
    	printTS(f.interleave(tsshort,tsshort));
    	
    	Set<String> hands = new HashSet<>();
    	hands.add("a1");
    	printTS(f.interleave(tsshort,tsshort, hands));
    	hands.add("a2");
    	printTS(f.interleave(tsshort,tsshort, hands));
    }    
    

    @Test
    public void ciruit() {    	
    	printTS(f.transitionSystemFromCircuit(new SimpleCircuit()));    	
    }
    
    public class SimpleCircuit implements Circuit{
		@Override
		public Set<String> getInputPortNames() {
			Set<String> s = new HashSet<>();
			s.add("x1");
			s.add("x2");
			//s.add("x3");
			return s;
		}

		@Override
		public Set<String> getRegisterNames() {
			Set<String> s = new HashSet<>();
			s.add("r1");
			s.add("r2");
			//s.add("r3");
			return s;
		}

		@Override
		public Set<String> getOutputPortNames() {
			Set<String> s = new HashSet<>();
			s.add("y1");
			s.add("y2");
			//s.add("y3");
			return s;
		}
		
		@Override
		public Map<String, Boolean> updateRegisters(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
			Map<String, Boolean> a = new HashMap<String, Boolean>();
			a.put("r1", inputs.get("x1")&inputs.get("x2"));
			a.put("r2", registers.get("r1")^registers.get("r2"));
			//a.put("r3", !registers.get("r1"));
			return a;
		}

		@Override
		public Map<String, Boolean> computeOutputs(Map<String, Boolean> inputs, Map<String, Boolean> registers) {
			Map<String, Boolean> a = new HashMap<String, Boolean>();
			a.put("y1", inputs.get("x1")&registers.get("r1"));
			a.put("y2", registers.get("r1")|registers.get("r2"));
			return a;
		}    	
    
    }
}
