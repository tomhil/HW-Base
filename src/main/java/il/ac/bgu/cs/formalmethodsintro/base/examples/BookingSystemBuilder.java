package il.ac.bgu.cs.formalmethodsintro.base.examples;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.Transition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;

// Example 2.29 in the book
public class BookingSystemBuilder {
	static FvmFacade fvmFacadeImpl = FvmFacade.get();

	public enum State {
		S0, S1
	}

	public enum Action {
		scan, store, prt_cmd, print
	}

	public enum AP {
	}

	static public TransitionSystem<State, Action, AP> buildBCR() {
		TransitionSystem<State, Action, AP> ts;
		ts = FvmFacade.get().createTransitionSystem();

		ts.setName("BCR");

		ts.addState(State.S1);
		ts.addInitialState(State.S0);

		ts.addAction(Action.scan);
		ts.addAction(Action.store);

		ts.addTransition(new Transition<>(State.S0, Action.scan, State.S1));
		ts.addTransition(new Transition<>(State.S1, Action.store, State.S0));

		return ts;
	}

	static public TransitionSystem<State, Action, AP> buildBP() {
		TransitionSystem<State, Action, AP> ts;
		ts = FvmFacade.get().createTransitionSystem();

		ts.setName("BP");

		ts.addState(State.S1);
		ts.addInitialState(State.S0);

		ts.addAction(Action.prt_cmd);
		ts.addAction(Action.store);

		ts.addTransition(new Transition<>(State.S0, Action.store, State.S1));
		ts.addTransition(new Transition<>(State.S1, Action.prt_cmd, State.S0));

		return ts;
	}

	static public TransitionSystem<State, Action, AP> buildPrinter() {
		TransitionSystem<State, Action, AP> ts;
		ts = FvmFacade.get().createTransitionSystem();

		ts.setName("Printer");

		ts.addState(State.S0);
		ts.addState(State.S1);
		ts.addInitialState(State.S0);

		ts.addAction(Action.prt_cmd);
		ts.addAction(Action.print);

		ts.addTransition(new Transition<>(State.S0, Action.prt_cmd, State.S1));
		ts.addTransition(new Transition<>(State.S1, Action.print, State.S0));

		return ts;
	}

}
