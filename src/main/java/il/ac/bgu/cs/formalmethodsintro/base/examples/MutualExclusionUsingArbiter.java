package il.ac.bgu.cs.formalmethodsintro.base.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.Transition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;

// Figure 2.12 in the book
public class MutualExclusionUsingArbiter {
    public enum TsState { NonCrit, Crit }
    public enum ArState { Unlock, Lock }
    public enum MuAction{ Request, Release }
    
	static final FvmFacade FVM_FACADE_IMPL = FvmFacade.get();
	
	static public TransitionSystem<TsState, MuAction, String> buildP() {
		TransitionSystem<TsState, MuAction, String> ts = FVM_FACADE_IMPL.createTransitionSystem();

		ts.addAllStates(TsState.values());
        ts.addAllActions(MuAction.values());
		ts.addInitialState(TsState.NonCrit);

		ts.addTransitionFrom(TsState.NonCrit).action(MuAction.Request).to(TsState.Crit);
        ts.addTransitionFrom(TsState.Crit).action(MuAction.Release).to(TsState.NonCrit);
        return ts;
    }

 
	static public TransitionSystem<ArState, MuAction, String> buildArbiter() {
		TransitionSystem<ArState, MuAction, String> ts = FVM_FACADE_IMPL.createTransitionSystem();

		ts.addAllStates(ArState.values());
        ts.addAllActions(MuAction.values());
		ts.addInitialState(ArState.Unlock);

		ts.addTransition(new Transition<>(ArState.Unlock, MuAction.Request, ArState.Lock));
		ts.addTransition(new Transition<>(ArState.Lock, MuAction.Release, ArState.Unlock));

        return ts;
    }

}
