package il.ac.bgu.cs.formalmethodsintro.base;

import java.util.Map.Entry;
import java.util.Set;

import org.junit.Test;
import org.svvrl.goal.core.util.HashSet;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.GraphvizPainter;

public class testVerification {
    private static FvmFacade f = FvmFacade.get();
	@Test
    public void testProduct(){
        TransitionSystem<String, String, String> ts = getTs1();
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
        Automaton<String, String> aut = getAut1();
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(f.product(ts, aut)));
        System.out.println(f.verifyAnOmegaRegularProperty(ts, aut));
        aut = getAut2();
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(f.product(ts, aut)));
        System.out.println(f.verifyAnOmegaRegularProperty(ts, aut));
        System.out.println(printAutomaton(getAut3()));
        System.out.println(printAutomaton3(f.GNBA2NBA(getAut3())));
    }

    //bad attempt to view as ts
	private String printAutomaton3(Automaton<?, String> aut) {
        return GraphvizPainter.toStringPainter().makeDotCode(autAsTs(aut));
    }

    private <A,B> TransitionSystem autAsTs(MultiColorAutomaton<A, ?> aut) {
        TransitionSystem<A, String, Integer> TS = new TransitionSystem<>();
        TS.setName("translated_aut");
        aut.getTransitions().entrySet().stream()
    			.forEach(entry->
    				entry.getValue().entrySet().stream().forEach(subEntry->
    					subEntry.getValue().stream().forEach(to->{
    						TS.addTransition(new TSTransition<A, String>(entry.getKey(), subEntry.getKey().toString(), to));
                        })));
        
        for(A s : aut.getInitialStates()){
            TS.addInitialState(s);
        }

        for(int color : aut.getColors()){
            for(A s : aut.getAcceptingStates(color))
                TS.addToLabel(s, color);
        }
        return TS;
    }

    // bad attempt to view as ts
	private String printAutomaton2(Automaton<?, String> aut) {
        return GraphvizPainter.toStringPainter().makeDotCode(f.product(getTsALL(), aut));
    }

	private String printAutomaton(MultiColorAutomaton<?, String> aut) {
		StringBuilder sb = new StringBuilder();
		for(int color : aut.getColors()) {
			sb.append("color ");
			sb.append(color);
			sb.append(": ");
			sb.append(aut.getAcceptingStates(color));
			sb.append("\n");
		}
		sb.append("inits ");
		sb.append(aut.getInitialStates());
		sb.append("\n");
		for(Entry<?, ?> t : aut.getTransitions().entrySet()) {
			sb.append("state ");
			sb.append(t.getKey());
			sb.append(" -> ");
			sb.append(t.getValue());
			sb.append("\n");
		}
		return sb.toString();
	}
	private TransitionSystem<String, String, String> getTs1() {
		TransitionSystem<String, String, String> ts = new TransitionSystem<>();
        ts.setName("ts_test_product");
        ts.addTransition(new TSTransition<String, String>("s0", "b", "s1"));
        ts.addTransition(new TSTransition<String, String>("s0", "a", "s3"));
        ts.addTransition(new TSTransition<String, String>("s3", "c", "s1"));
        ts.addTransition(new TSTransition<String, String>("s1", "a", "s4"));
        ts.addTransition(new TSTransition<String, String>("s4", "c", "s1"));
        ts.addTransition(new TSTransition<String, String>("s4", "b", "s5"));
        ts.addTransition(new TSTransition<String, String>("s5", "b", "s1"));
        ts.addTransition(new TSTransition<String, String>("s5", "a", "s2"));
        ts.addTransition(new TSTransition<String, String>("s2", "c", "s1"));
        ts.addInitialState("s0");
        ts.addToLabel("s0", "A");ts.addToLabel("s0", "B");
        ts.addToLabel("s3", "A");ts.addToLabel("s3", "C");
        ts.addToLabel("s1", "A");ts.addToLabel("s1", "B");ts.addToLabel("s1", "C");
        ts.addToLabel("s4", "A");ts.addToLabel("s4", "C");
        ts.addToLabel("s2", "C");ts.addToLabel("s2", "B");
        ts.addToLabel("s5", "A");ts.addToLabel("s5", "B");
		return ts;
    }

    private TransitionSystem<String, String, String> getTsALL() {
		TransitionSystem<String, String, String> ts = new TransitionSystem<>();
        ts.setName("ts_all_label");
        ts.addTransition(new TSTransition<String, String>("s0", "a", "s1"));
        ts.addTransition(new TSTransition<String, String>("s0", "a", "s2"));
        ts.addTransition(new TSTransition<String, String>("s1", "b", "s0"));
        ts.addTransition(new TSTransition<String, String>("s1", "b", "s2"));
        ts.addTransition(new TSTransition<String, String>("s2", "c", "s0"));
        ts.addTransition(new TSTransition<String, String>("s2", "c", "s1"));
        ts.addInitialState("s0");ts.addInitialState("s1");ts.addInitialState("s2");
        ts.addToLabel("s0", "A");
        ts.addToLabel("s1", "B");
        ts.addToLabel("s2", "A");ts.addToLabel("s2", "B");
        return ts;
    }
    
    private Automaton<String, String> getAutALL() {
		Automaton<String, String> aut = new Automaton<>();
        Set<String> A = new HashSet<>();        A.add("A");
        Set<String> B = new HashSet<>();        B.add("B");
        Set<String> C = new HashSet<>();        C.add("C");

        Set<String> AB = new HashSet<>();
        AB.add("A");        AB.add("B");
        
        Set<String> AC = new HashSet<>();
        AC.add("A");        AC.add("C");  
        
        Set<String> BC = new HashSet<>();
        BC.add("B");        BC.add("C");
        
        Set<String> ABC = new HashSet<>();
        ABC.add("A");        ABC.add("B");       ABC.add("C");
        
        aut.setInitial("q0");				     aut.setAccepting("q0");
        
        aut.addTransition("q0", A, "q0");   aut.addTransition("q0", B, "q0");   aut.addTransition("q0", C, "q0");
        aut.addTransition("q0", AB, "q0");  aut.addTransition("q0", AC, "q0");  aut.addTransition("q0", BC, "q0");
        aut.addTransition("q0", ABC, "q0");
        return aut;
	}
	
	private Automaton<String, String> getAut1() {
		Automaton<String, String> aut = new Automaton<>();
        Set<String> A = new HashSet<>();        A.add("A");
        Set<String> B = new HashSet<>();        B.add("B");
        Set<String> C = new HashSet<>();        C.add("C");

        Set<String> AB = new HashSet<>();
        AB.add("A");        AB.add("B");
        
        Set<String> AC = new HashSet<>();
        AC.add("A");        AC.add("C");  
        
        Set<String> BC = new HashSet<>();
        BC.add("B");        BC.add("C");
        
        Set<String> ABC = new HashSet<>();
        ABC.add("A");        ABC.add("B");       ABC.add("C");
        
        aut.setInitial("q0");				     aut.setAccepting("q3");
        
        aut.addTransition("q0", AC, "q0");       aut.addTransition("q0", C, "q0");       aut.addTransition("q0", BC, "q0");       aut.addTransition("q0", ABC, "q0");
        aut.addTransition("q0", B, "q1");        aut.addTransition("q0", AB, "q1");

        aut.addTransition("q1", A, "q2");       aut.addTransition("q1", AB, "q2");	aut.addTransition("q1", AC, "q2");	aut.addTransition("q1", ABC, "q2");
        aut.addTransition("q1", B, "q1");
        aut.addTransition("q1", C, "q0");        aut.addTransition("q1", BC, "q0");
        
        aut.addTransition("q2", C, "q0");        aut.addTransition("q2", BC, "q0");	aut.addTransition("q2", AC, "q0");	aut.addTransition("q2", ABC, "q0");
        aut.addTransition("q2", A, "q3");        aut.addTransition("q2", B, "q3");        aut.addTransition("q2", AB, "q3");
		return aut;
	}
	
	private Automaton<String, String> getAut2() {
		Automaton<String, String> aut = new Automaton<>();
        Set<String> A = new HashSet<>();        A.add("A");
        Set<String> B = new HashSet<>();        B.add("B");
        Set<String> C = new HashSet<>();        C.add("C");

        Set<String> AB = new HashSet<>();
        AB.add("A");        AB.add("B");
        
        Set<String> AC = new HashSet<>();
        AC.add("A");        AC.add("C");  
        
        Set<String> BC = new HashSet<>();
        BC.add("B");        BC.add("C");
        
        Set<String> ABC = new HashSet<>();
        ABC.add("A");        ABC.add("B");       ABC.add("C");
        
        aut.setInitial("p");
        aut.setAccepting("q");
        aut.addTransition("p", B, "p");	aut.addTransition("p", C, "p");	aut.addTransition("p", BC, "p");
        aut.addTransition("p", A, "q");	aut.addTransition("p", AB, "q");	aut.addTransition("p", AC, "q");	aut.addTransition("p", ABC, "q");
        aut.addTransition("q", A, "q");	aut.addTransition("q", AB, "q");	aut.addTransition("q", AC, "q");	aut.addTransition("q", ABC, "q");
        aut.addTransition("q", B, "p");	aut.addTransition("q", C, "p");	aut.addTransition("q", BC, "p");        
		return aut;
	}
	
	private MultiColorAutomaton<String, String> getAut3() {
		MultiColorAutomaton<String, String> aut = new MultiColorAutomaton<>();
        Set<String> A = new HashSet<>();        A.add("A");
        Set<String> B = new HashSet<>();        B.add("B");

        Set<String> AB = new HashSet<>();
        AB.add("A");        AB.add("B");
        
        aut.setInitial("q1");
        aut.setAccepting("q0",0);
        aut.setAccepting("q2",2);
        aut.addTransition("q1", A, "q0");
        aut.addTransition("q1", B, "q2");
        aut.addTransition("q1", A, "q1");	aut.addTransition("q1", B, "q1");	aut.addTransition("q1", AB, "q1");
        aut.addTransition("q0", A, "q1");	aut.addTransition("q0", B, "q1");	aut.addTransition("q0", AB, "q1");
        aut.addTransition("q2", A, "q1");	aut.addTransition("q2", B, "q1");	aut.addTransition("q2", AB, "q1");
		return aut;
	}
}
