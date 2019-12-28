package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.InputStream;
import java.util.*;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.channelsystem.ChannelSystem;
import il.ac.bgu.cs.formalmethodsintro.base.circuits.Circuit;
import il.ac.bgu.cs.formalmethodsintro.base.exceptions.StateNotFoundException;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.*;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.AlternatingSequence;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import il.ac.bgu.cs.formalmethodsintro.base.verification.VerificationResult;

/**
 * Interface for the entry point class to the HW in this class. Our
 * client/testing code interfaces with the student solutions through this
 * interface only. <br>
 */
public class FvmFacade {

    private static FvmFacade INSTANCE = null;

    /**
     * @return an instance of this class.
     */
    public static FvmFacade get() {
        if (INSTANCE == null) {
            INSTANCE = new FvmFacade();
        }
        return INSTANCE;
    }

    /**
     * Checks whether a transition system is action deterministic. I.e., if for
     * any given p and α there exists only a single tuple (p,α,q) in →. Note
     * that this must be true even for non-reachable states.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is deterministic.
     */
    public <S, A, P> boolean isActionDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;
        Set<S> states = ts.getStates();
        Set<A> actions = ts.getActions();
        for (S state : states) {
            for (A action : actions) {
                if ((post(ts, state, action)).size() > 1)
                    return false;
            }
        }
        return true;
    }

    /**
     * Checks whether an action is ap-deterministic (as defined in class), in
     * the context of a given {@link TransitionSystem}.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @return {@code true} iff the action is ap-deterministic.
     */
    public <S, A, P> boolean isAPDeterministic(TransitionSystem<S, A, P> ts) {
        if (ts.getInitialStates().size() > 1)
            return false;
        Set<S> states = ts.getStates();
        for (S state : states) {
            Set<Set<P>> labales = new HashSet<>();
            Set<S> posts = post(ts, state);
            for (S post : posts) {
                if (labales.contains(ts.getLabel(post)))
                    return false;
                labales.add(ts.getLabel(post));
            }
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an execution of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution of {@code ts}.
     * @return {@code true} iff {@code e} is an execution of {@code ts}.
     */
    public <S, A, P> boolean isExecution(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isInitialExecutionFragment(ts, e) && isMaximalExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is an execution fragment of a
     * {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an execution fragment of
     *            {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        while (e.size() > 1) {
            S from = e.head();
            A action = e.tail().head();
            e = e.tail().tail();
            S to = e.head();
            if (!ts.getTransitions().contains(new TSTransition<>(from, action, to)))
                return false;
        }
        return true;
    }

    /**
     * Checks whether an alternating sequence is an initial execution fragment
     * of a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be an initial execution
     *            fragment of {@code ts}.
     * @return {@code true} iff {@code e} is an execution fragment of
     * {@code ts}.
     */
    public <S, A, P> boolean isInitialExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return ts.getInitialStates().contains(e.head()) && isExecutionFragment(ts, e);
    }

    /**
     * Checks whether an alternating sequence is a maximal execution fragment of
     * a {@link TransitionSystem}, as defined in class.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param <P> Type of atomic propositions.
     * @param ts  The transition system being tested.
     * @param e   The sequence that may or may not be a maximal execution fragment
     *            of {@code ts}.
     * @return {@code true} iff {@code e} is a maximal fragment of {@code ts}.
     */
    public <S, A, P> boolean isMaximalExecutionFragment(TransitionSystem<S, A, P> ts, AlternatingSequence<S, A> e) {
        return isExecutionFragment(ts, e) && isStateTerminal(ts, e.last());
    }

    /**
     * Checks whether a state in {@code ts} is terminal.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   The state being tested for terminality.
     * @return {@code true} iff state {@code s} is terminal in {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> boolean isStateTerminal(TransitionSystem<S, A, ?> ts, S s) {
        if (ts == null || !ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        return post(ts, s).isEmpty();
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Post(s)}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, S s) {
        if (ts == null || !ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<S>();
        for (TSTransition<S, ?> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s))
                output.add(transition.getTo());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Post(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        if (ts != null && !ts.getStates().containsAll(c))
            throw new StateNotFoundException("public <S> Set<S> post(TransitionSystem<S, ?, ?> ts, Set<S> c)- Ts is null");
        Set<S> output = new HashSet<S>();
        for (S s : c) {
            output.addAll(post(ts, s));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from
     * {@code s}, when action {@code a} is selected.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (!ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<S>();
        for (TSTransition<S, A> transition : ts.getTransitions()) {
            if (transition.getFrom().equals(s) && transition.getAction().equals(a))
                output.add(transition.getTo());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transition to from any state
     * in {@code c}, when action {@code a} is selected.
     */
    public <S, A> Set<S> post(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        Set<S> output = new HashSet<S>();
        for (S s : c) {
            output.addAll(post(ts, s, a));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @return All the states in {@code Pre(s)}, in the context of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, S s) {
        Set<S> output = new HashSet<S>();
        for (TSTransition<S, ?> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s))
                output.add(transition.getFrom());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param ts  Transition system of {@code s}.
     * @param c   States in {@code ts}.
     * @return All the states in {@code Pre(s)} where {@code s} is a member of
     * {@code c}, in the context of {@code ts}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) {
        if (ts != null && !ts.getStates().containsAll(c))
            throw new StateNotFoundException(" public <S> Set<S> pre(TransitionSystem<S, ?, ?> ts, Set<S> c) - Ts is null");
        Set<S> output = new HashSet<S>();
        for (S s : c) {
            output.addAll(pre(ts, s));
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param s   A state in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * {@code s}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, S s, A a) {
        if (ts == null || !ts.getStates().contains(s))
            throw new StateNotFoundException(s);
        Set<S> output = new HashSet<S>();
        for (TSTransition<S, A> transition : ts.getTransitions()) {
            if (transition.getTo().equals(s) && transition.getAction().equals(a))
                output.add(transition.getFrom());
        }
        return output;
    }

    /**
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @param c   Set of states in {@code ts}.
     * @param a   An action.
     * @return All the states that {@code ts} might transitioned from, when in
     * any state in {@code c}, and the last action was {@code a}.
     * @throws StateNotFoundException if {@code s} is not a state of {@code ts}.
     */
    public <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a) {
        if (ts == null)
            throw new StateNotFoundException(" <S, A> Set<S> pre(TransitionSystem<S, A, ?> ts, Set<S> c, A a)- Ts is null");
        Set<S> output = new HashSet<S>();
        for (S s : c) {
            output.addAll(pre(ts, s, a));
        }
        return output;
    }


    public static <T> LinkedList<T> convertSetToList(Set<T> set) {
        // create an empty list
        LinkedList<T> list = new LinkedList<T>();

        // push each element in the set into the list
        for (T t : set)
            list.push(t);

        // return the list
        return list;
    }

    /**
     * Implements the {@code reach(TS)} function.
     *
     * @param <S> Type of states.
     * @param <A> Type of actions.
     * @param ts  Transition system of {@code s}.
     * @return All states reachable in {@code ts}.
     */
    public <S, A> Set<S> reach(TransitionSystem<S, A, ?> ts) {
        LinkedList<S> states = new LinkedList<>(ts.getInitialStates());
        Set<S> output = new HashSet<S>();
        while (!states.isEmpty()) {
            S s = states.remove();
            output.add(s);
            Set<S> posts = post(ts, s);
            //Prevention of Circuits
            for (S post : posts) {
                if (!output.contains(post))
                    states.add(post);
            }
        }
        return output;
    }

    private <S1, S2> Set<Pair<S1, S2>> CartesianProduct(Set<S1> g1, Set<S2> g2) {
        Set<Pair<S1, S2>> output = new HashSet<>();
        for (S1 s1 : g1) {
            for (S2 s2 : g2) {
                output.add(new Pair<S1, S2>(s1, s2));
            }
        }
        return output;
    }

    private <S1> Set<List<S1>> CartesianProductForSet(Set<List<S1>> g1, Set<S1> g2) {
        Set<List<S1>> output = new HashSet<>();
        for (List<S1> s1 : g1) {
            for (S1 s2 : g2) {
                List<S1> toInsert = new ArrayList<>(s1);
                toInsert.add(s2);
                output.add(toInsert);
            }
        }
        return output;
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1> Type of states in the first system.
     * @param <S2> Type of states in the first system.
     * @param <A>  Type of actions (in both systems).
     * @param <P>  Type of atomic propositions (in both systems).
     * @param ts1  The first transition system.
     * @param ts2  The second transition system.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2) {
        return interleave(ts1, ts2, new HashSet<>());
    }

    /**
     * Compute the synchronous product of two transition systems.
     *
     * @param <S1>               Type of states in the first system.
     * @param <S2>               Type of states in the first system.
     * @param <A>                Type of actions (in both systems).
     * @param <P>                Type of atomic propositions (in both systems).
     * @param ts1                The first transition system.
     * @param ts2                The second transition system.
     * @param handShakingActions Set of actions both systems perform together.
     * @return A transition system that represents the product of the two.
     */
    public <S1, S2, A, P> TransitionSystem<Pair<S1, S2>, A, P> interleave(TransitionSystem<S1, A, P> ts1,
                                                                          TransitionSystem<S2, A, P> ts2, Set<A> handShakingActions) {

        TransitionSystem<Pair<S1, S2>, A, P> output = new TransitionSystem<>();

        for (Pair<S1, S2> initState : CartesianProduct(ts1.getInitialStates(), ts2.getInitialStates())) {
            output.addInitialState(initState);
        }

        output.addAllStates(CartesianProduct(ts1.getStates(), ts2.getStates()));

        output.addAllActions(ts1.getActions());
        output.addAllActions(ts2.getActions());

        output.addAllAtomicPropositions(ts1.getAtomicPropositions());
        output.addAllAtomicPropositions(ts2.getAtomicPropositions());


        //Transaction part
        for (A action : output.getActions()) {
            if (handShakingActions.contains(action)) {
                for (TSTransition<S1, A> tst1 : ts1.getTransitions()) {
                    for (TSTransition<S2, A> tst2 : ts2.getTransitions()) {
                        //if i found transition with the handshake action add it to new ts
                        if (tst1.getAction().equals(action) && tst2.getAction().equals(action)) {
                            TSTransition<Pair<S1, S2>, A> handshake = new TSTransition<>
                                    (new Pair<S1, S2>(tst1.getFrom(), tst2.getFrom()),
                                            action,
                                            new Pair<S1, S2>(tst1.getTo(), tst2.getTo()));
                            output.addTransition(handshake);
                        }
                    }
                }
            } else {
                //if this not handshake action -ts1
                for (TSTransition<S1, A> tst1 : ts1.getTransitions()) {
                    if (tst1.getAction().equals(action)) {
                        for (Pair<S1, S2> from : output.getStates()) {
                            if (tst1.getFrom().equals(from.first)) {
                                for (Pair<S1, S2> to : output.getStates()) {
                                    if (tst1.getTo().equals(to.first) && from.second.equals(to.second)) {
                                        output.addTransition(new TSTransition<>(from, action, to));
                                    }
                                }
                            }
                        }
                    }
                }

                //if this not handshake action -ts2
                for (TSTransition<S2, A> tst2 : ts2.getTransitions()) {
                    if (tst2.getAction().equals(action)) {
                        for (Pair<S1, S2> from : output.getStates()) {
                            if (tst2.getFrom().equals(from.second)) {
                                for (Pair<S1, S2> to : output.getStates()) {
                                    if (tst2.getTo().equals(to.second) && from.first.equals(to.first)) {
                                        output.addTransition(new TSTransition<>(from, action, to));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }


        //label part
        for (Pair<S1, S2> state : output.getStates()) {
            for (P label : ts1.getLabel(state.first)) {
                output.addToLabel(state, label);
            }
            for (P label : ts2.getLabel(state.second)) {
                output.addToLabel(state, label);
            }
        }
        return output;
    }

    /**
     * Creates a new {@link ProgramGraph} object.
     *
     * @param <L> Type of locations in the graph.
     * @param <A> Type of actions of the graph.
     * @return A new program graph instance.
     */
    public <L, A> ProgramGraph<L, A> createProgramGraph() {
        return new ProgramGraph<>();
    }

    /**
     * Interleaves two program graphs.
     *
     * @param <L1> Type of locations in the first graph.
     * @param <L2> Type of locations in the second graph.
     * @param <A>  Type of actions in BOTH GRAPHS.
     * @param pg1  The first program graph.
     * @param pg2  The second program graph.
     * @return Interleaved program graph.
     */
    public <L1, L2, A> ProgramGraph<Pair<L1, L2>, A> interleave(ProgramGraph<L1, A> pg1, ProgramGraph<L2, A> pg2) {
        ProgramGraph<Pair<L1, L2>, A> output = new ProgramGraph<Pair<L1, L2>, A>();

        for (Pair<L1, L2> location : CartesianProduct(pg1.getLocations(), pg2.getLocations())) {
            output.addLocation(location);
        }

        for (Pair<L1, L2> initLoc : CartesianProduct(pg1.getInitialLocations(), pg2.getInitialLocations())) {
            output.setInitial(initLoc, true);
        }

        for (List<String> initCondition : pg1.getInitalizations()) {
            output.addInitalization(initCondition);
        }

        for (List<String> initCondition : pg2.getInitalizations()) {
            output.addInitalization(initCondition);
        }

        //Transaction part
        for (PGTransition<L1, A> transaction : pg1.getTransitions()) {
            for (L2 permanent : pg2.getLocations()) {
                output.addTransition(new PGTransition<Pair<L1, L2>, A>(
                        new Pair<L1, L2>(transaction.getFrom(), permanent),
                        transaction.getCondition(),
                        transaction.getAction(),
                        new Pair<L1, L2>(transaction.getTo(), permanent)
                ));
            }
        }
        for (PGTransition<L2, A> transaction : pg2.getTransitions()) {
            for (L1 permanent : pg1.getLocations()) {
                output.addTransition(new PGTransition<Pair<L1, L2>, A>(
                        new Pair<L1, L2>(permanent, transaction.getFrom()),
                        transaction.getCondition(),
                        transaction.getAction(),
                        new Pair<L1, L2>(permanent, transaction.getFrom())
                ));
            }
        }
        return output;

    }

    private Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> CircuitStates(Set<String> registers, Set<String> inputs) {
        Set<Map<String, Boolean>> registersPowerGroup = PowerGroup(registers);
        Set<Map<String, Boolean>> inputsPowerGroup = PowerGroup(inputs);
        return CartesianProduct(inputsPowerGroup, registersPowerGroup);
    }

    private Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> GetInitStatesFromCircuit(Set<String> registerNames, Set<String> inputPortNames) {
        Set<Map<String, Boolean>> inputsPowerGroup = PowerGroup(inputPortNames);
        Set<Map<String, Boolean>> initRegistersGroup = new HashSet<>();
        Map<String, Boolean> initRegisters = new HashMap<>();
        for (String register : registerNames) {
            initRegisters.put(register, false);
        }
        initRegistersGroup.add(initRegisters);
        return CartesianProduct(inputsPowerGroup, initRegistersGroup);
    }

    private Set<Map<String, Boolean>> PowerGroup(Set<String> group) {
        Set<Map<String, Boolean>> powerGroup = new HashSet<>();
        for (int i = 0; i < Math.pow(2, group.size()); i++) {
            Map<String, Boolean> team = new HashMap<>();
            for (int j = 0; j < group.size(); j++) {
                if ((i & (1 << j)) > 0) {
                    team.put((String) group.toArray()[j], true);
                } else {
                    team.put((String) group.toArray()[j], false);
                }
            }
            powerGroup.add(team);
        }
        return powerGroup;
    }


    /**
     * Creates a {@link TransitionSystem} representing the passed circuit.
     *
     * @param c The circuit to translate into a {@link TransitionSystem}.
     * @return A {@link TransitionSystem} representing {@code c}.
     */
    public TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object>
    transitionSystemFromCircuit(
            Circuit c) {
        TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> output = new TransitionSystem<>();

        //state- 2^|X| x 2^|R|
        output.addAllStates(CircuitStates(c.getRegisterNames(), c.getInputPortNames()));

        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> initStates = GetInitStatesFromCircuit(c.getRegisterNames(), c.getInputPortNames());
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> initState : initStates) {
            output.addInitialState(initState);
        }

        //action - {0,1}^|X|
        output.addAllActions(PowerGroup(c.getInputPortNames()));

        //atomic Propositions- all the inputs ,outputs and registers.
        output.addAllAtomicPropositions(makeAtomicProposition(c.getInputPortNames(), c.getOutputPortNames(), c.getRegisterNames()));

        //Transition ratio
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> from : output.getStates()) {
            for (Map<String, Boolean> action : output.getActions()) {
                Pair<Map<String, Boolean>, Map<String, Boolean>> to = new Pair<>(action,
                        c.updateRegisters(from.first, from.second));
                output.addTransition(new TSTransition<>(from, action, to));
            }
        }

        //label
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state : output.getStates()) {
            for (String label : ComputeLabel(state, c))
                output.addToLabel(state, label);
        }
        //remove unreach states
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> statesToRemove = GetStateToRemove(output);
        for (Pair<Map<String, Boolean>, Map<String, Boolean>> state:statesToRemove) {
            Set<TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>,Map<String, Boolean>>> toRemove=new HashSet<>();
            for (TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>,Map<String, Boolean>> transition: output.getTransitions()) {
                if(transition.getFrom().equals(state))
                    toRemove.add(transition);
            }
            for (TSTransition<Pair<Map<String, Boolean>, Map<String, Boolean>>,Map<String, Boolean>> transaction:toRemove) {
                    output.removeTransition(transaction);
            }
            output.removeState(state);
        }



        return output;
    }

    private Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> GetStateToRemove(TransitionSystem<Pair<Map<String, Boolean>, Map<String, Boolean>>, Map<String, Boolean>, Object> ts) {
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> statesReach = new HashSet<>(ts.getInitialStates());
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> tmpStates = new HashSet<>(ts.getInitialStates());
        while (!tmpStates.isEmpty()) {
            Pair<Map<String, Boolean>, Map<String, Boolean>> state = tmpStates.iterator().next();
            tmpStates.remove(state);
            for (Pair<Map<String, Boolean>, Map<String, Boolean>> postStates : post(ts, state)) {
                if (!statesReach.contains(postStates)) {
                    statesReach.add(postStates);
                    tmpStates.add(postStates);
                }
            }
        }
        Set<Pair<Map<String, Boolean>, Map<String, Boolean>>> output = new HashSet<>(ts.getStates());
        output.removeAll(statesReach);
        return output;
    }


    private Set<String> ComputeLabel(Pair<Map<String, Boolean>, Map<String, Boolean>> state, Circuit c) {
        Set<String> output = new HashSet<>();

        GetLabelFromMap(output, c.computeOutputs(state.first, state.second));
        GetLabelFromMap(output, state.first);
        GetLabelFromMap(output, state.second);

        return output;
    }

    private void GetLabelFromMap(Set<String> output, Map<String, Boolean> entries) {
        for (Map.Entry<String, Boolean> inputport : entries.entrySet()) {
            if (inputport.getValue())
                output.add(inputport.getKey());
        }
    }

    private Iterable<Object> makeAtomicProposition(Set<String> inputPortNames, Set<String> outputPortNames, Set<String> registerNames) {
        Set<Object> output = new HashSet<>(inputPortNames);
        output.addAll(outputPortNames);
        output.addAll(registerNames);
        return output;
    }


    /**
     * Creates a {@link TransitionSystem} from a program graph.
     *
     * @param <L>           Type of program graph locations.
     * @param <A>           Type of program graph actions.
     * @param pg            The program graph to be translated into a transition system.
     * @param actionDefs    Defines the effect of each action.
     * @param conditionDefs Defines the conditions (guards) of the program
     *                      graph.
     * @return A transition system representing {@code pg}.
     */
    //ts output need to be with: location- Pair of <L-location in pg, eval thats
    // map <var name, var val> , action- A and labal string
    public <L, A> TransitionSystem<Pair<L, Map<String, Object>>, A, String> transitionSystemFromProgramGraph(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs, Set<ConditionDef> conditionDefs) {

        TransitionSystem<Pair<L, Map<String, Object>>, A, String> output = new TransitionSystem<>();

        //init states
        for (L initLocation : pg.getInitialLocations()) {
            for (Map<String, Object> values : getInitValues(pg, actionDefs)) {
                output.addInitialState(new Pair<>(initLocation, values));
            }
        }

        //states and transitions
        Set<Pair<L, Map<String, Object>>> tmpState = new HashSet<>(output.getInitialStates());
        while (!tmpState.isEmpty()) {
            Pair<L, Map<String, Object>> from = tmpState.iterator().next();
            L location = from.first;
            Map<String, Object> eval = from.second;
            for (PGTransition<L, A> transaction : pg.getTransitions()) {
                if (transaction.getFrom().equals(location) && ConditionDef.evaluate(conditionDefs, eval, transaction.getCondition())) {
                    Pair<L, Map<String, Object>> to = new Pair<>(transaction.getTo(), ActionDef.effect(actionDefs, eval, transaction.getAction()));
                    if (!output.getStates().contains(to)) {
                        output.addState(to);
                        tmpState.add(to);
                    }
                    output.addAction(transaction.getAction());
                    output.addTransition(new TSTransition<>(from, transaction.getAction(), to));
                }
            }
            tmpState.remove(from);
        }

        //Labels and Atomic Proposition
        for (Pair<L, Map<String, Object>> state : output.getStates()) {
            if(!state.first.equals("")){
                output.addAtomicProposition(state.getFirst().toString());
                output.addToLabel(state, state.first.toString());
                for (Map.Entry<String, Object> eval : state.second.entrySet()) {
                    String atomicProposition= eval.getKey()+" = "+eval.getValue().toString();
                    output.addAtomicProposition(atomicProposition);
                    output.addToLabel(state,atomicProposition);
                }
            }
        }
        return output;
    }

    private Set<String> CleanCondition(String condition) {
        Set<String> output=new HashSet<>();
        if(condition.contains("&")){
            for (String cond:condition.split("&")) {
                output.addAll(CleanCondition(cond));
            }
        }else if( condition.contains("|")) {
            for (String cond : condition.split("|")) {
                output.addAll(CleanCondition(cond));
            }
        }else if( condition.contains("(") && condition.contains(")") ) {
            output.addAll(CleanCondition(condition.replaceAll("[\\[\\](){}]","")));
        }
        else{
            output.add(condition);
        }
        return output;
    }

    private <A, L> Set<Map<String, Object>> getInitValues(ProgramGraph<L, A> pg, Set<ActionDef> actionDefs) {
        Set<Map<String, Object>> output = new HashSet<>();
        for (List<String> conditionList : pg.getInitalizations()) {
            Map<String, Object> initialEvaluation = new HashMap<>();
            for (String condition : conditionList) {
                initialEvaluation = ActionDef.effect(actionDefs, initialEvaluation, condition);
            }
            output.add(initialEvaluation);
        }
        //g0 is empty
        if (output.isEmpty())
            output.add(new HashMap<>());
        return output;
    }


    /**
     * Creates a transition system representing channel system {@code cs}.
     *
     * @param <L> Type of locations in the channel system.
     * @param <A> Type of actions in the channel system.
     * @param cs  The channel system to be translated into a transition system.
     * @return A transition system representing {@code cs}.
     */
    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs) {

        Set<ActionDef> actions = Collections.singleton(new ParserBasedActDef());
        Set<ConditionDef> conditions = Collections.singleton(new ParserBasedCondDef());
        return transitionSystemFromChannelSystem(cs, actions, conditions);
    }

    public <L, A> TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> transitionSystemFromChannelSystem(
            ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String> output = new TransitionSystem<Pair<List<L>, Map<String, Object>>, A, String>();
        Set<String> conditionsProposition = new HashSet<>();

        //init States
        for (Pair<List<L>, Map<String, Object>> initState : getInitStates(cs, actions, conditions)) {
            output.addInitialState(initState);
        }
        //add init Atomic Proposition
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
            for (List<String> initConditionList : pg.getInitalizations()) {
                for (String initCond : initConditionList) {
                    output.addAtomicProposition(initCond);
                    conditionsProposition.add(initCond);
                }
            }
            for (L location : pg.getLocations()) {
                output.addAtomicProposition(location.toString());
            }
        }

        //states and transitions
        Set<Pair<List<L>, Map<String, Object>>> tmpState = new HashSet<>(output.getInitialStates());
        while (!tmpState.isEmpty()) {
            Pair<List<L>, Map<String, Object>> from = tmpState.iterator().next();
            List<L> locations = from.first;
            Map<String, Object> eval = new HashMap<String, Object>(from.second);
            for (int i = cs.getProgramGraphs().size() - 1; i >= 0; i--) {
                ProgramGraph<L, A> pg = cs.getProgramGraphs().get(cs.getProgramGraphs().size() - 1 - i);
                L location = locations.get(i);
                for (PGTransition<L, A> transaction : pg.getTransitions()) {
                    if (transaction.getFrom().equals(location) && ConditionDef.evaluate(conditions, eval, transaction.getCondition())) {
                        List<L> toLocations = new ArrayList<>(locations);
                        toLocations.set(i, transaction.getTo());
                        Pair<List<L>, Map<String, Object>> to = new Pair<>(toLocations, ActionDef.effect(actions, eval, transaction.getAction()));
                        if (!output.getStates().contains(to)) {
                            output.addState(to);
                            tmpState.add(to);
                        }
                        output.addAction(transaction.getAction());
                        conditionsProposition.add(transaction.getCondition());
                        output.addAtomicProposition(transaction.getCondition());
                        output.addTransition(new TSTransition(from, transaction.getAction(), to));
                    }
                }
            }
            tmpState.remove(from);
        }
        //Labels
        for (Pair<List<L>, Map<String, Object>> state : output.getStates()) {
            for (L location : state.getFirst()) {
                output.addAtomicProposition(location.toString());
            }
            for (String condition : conditionsProposition) {
                if (ConditionDef.evaluate(conditions, state.second, condition))
                    output.addToLabel(state, condition);
            }
        }
        return output;
    }

    private <L, A> Set<Pair<List<L>, Map<String, Object>>> getInitStates(ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        Set<List<L>> initLocations = getInitLocations(cs);
        Set<Map<String, Object>> evals = getInitValues(cs, actions, conditions);
        return CartesianProduct(initLocations, evals);
    }

    protected <L, A> Set<List<L>> getInitLocations(ChannelSystem<L, A> cs) {
        int i = cs.getProgramGraphs().size() - 1;
        Set<List<L>> output = CartesianProductForSet(new HashSet<List<L>>(Arrays.asList(new ArrayList<L>())), cs.getProgramGraphs().get(i).getInitialLocations());
        i--;
        while (i >= 0) {
            output = CartesianProductForSet(output, cs.getProgramGraphs().get(i).getInitialLocations());
            i--;
        }
        return output;
    }

    private <L, A> Set<Map<String, Object>> getInitValues(ChannelSystem<L, A> cs, Set<ActionDef> actions, Set<ConditionDef> conditions) {
        Set<Map<String, Object>> output = new HashSet<>();
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
            for (List<String> condList : pg.getInitalizations()) {
                Map<String, Object> initialEvaluation = new HashMap<>();
                for (String condition : condList) {
                    initialEvaluation = ActionDef.effect(actions, initialEvaluation, condition);
                }
//                if (checkAllInitalizationsCondition(cs, conditions, initialEvaluation))
                    output.add(initialEvaluation);
            }
        }
        if(output.isEmpty())
            output.add(new HashMap<>());
        return output;
    }

    private <L, A> boolean checkAllInitalizationsCondition(ChannelSystem<L, A> cs, Set<ConditionDef> conditions, Map<String, Object> candidate) {
        for (ProgramGraph<L, A> pg : cs.getProgramGraphs()) {
            for (List<String> condList : pg.getInitalizations()) {
                for (String cond : condList) {
                    if (!ConditionDef.evaluate(conditions, candidate, cond))
                        return false;
                }
            }
        }
        return true;
    }


    /**
     * Construct a program graph from nanopromela code.
     *
     * @param filename The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(String filename) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaFile(filename));
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param nanopromela The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromelaString(String nanopromela) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.pareseNanoPromelaString(nanopromela));
    }

    /**
     * Construct a program graph from nanopromela code.
     *
     * @param inputStream The nanopromela code.
     * @return A program graph for the given code.
     * @throws Exception If the code is invalid.
     */
    public ProgramGraph<String, String> programGraphFromNanoPromela(InputStream inputStream) throws Exception {
        return programGraphFromNanoPromela(NanoPromelaFileReader.parseNanoPromelaStream(inputStream));
    }


    public ProgramGraph<String, String> programGraphFromNanoPromela(NanoPromelaParser.StmtContext root) throws Exception {
        ProgramGraph<String, String> output = createProgramGraph();
        Set<String> locations = new HashSet<>();
        Set<PGTransition<String, String>> transitions = new HashSet<>();
        getStateAndTransitions(root, locations, transitions);
        //add all the location
        for (String location : locations) {
            output.addLocation(location);
            if (location.equals(root.getText()))
                output.setInitial(location, true);
        }
        Set<PGTransition<String, String>> transitionToRemove = new HashSet<>();
        for (PGTransition<String, String> transition : transitions) {
            if (!output.getLocations().contains(transition.getFrom()))
                transitionToRemove.add(transition);
        }
        transitions.removeAll(transitionToRemove);
        //add transition and
        for (PGTransition<String, String> transition : transitions) {
            output.addTransition(transition);
        }
        //remove unreachable states and transactions
        RemoveUnreachStatesAndTransaction(output);
        return output;
    }

    private void RemoveUnreachStatesAndTransaction(ProgramGraph<String, String> pg) {
        Set<String> unReachLocation=new HashSet<>(pg.getLocations());
        Set<String> tmpLocation=new HashSet<>(pg.getInitialLocations());
        unReachLocation.removeAll(tmpLocation);
        while(!tmpLocation.isEmpty()){
            String location=tmpLocation.iterator().next();
            for (PGTransition<String,String> transaction:pg.getTransitions()) {
                if(transaction.getFrom().equals(location)){
                    if(unReachLocation.contains(transaction.getTo())){
                        unReachLocation.remove(transaction.getTo());
                        tmpLocation.add(transaction.getTo());
                    }
                }
            }
            tmpLocation.remove(location);
        }
        for (String locationToRemove:unReachLocation) {
            Set<PGTransition<String,String>> toRemove=new HashSet<>();
            for (PGTransition<String,String> transaction:pg.getTransitions()) {
                if(transaction.getFrom().equals(locationToRemove))
                    toRemove.add(transaction);
            }
            for (PGTransition<String,String> transaction:toRemove) {
                    pg.removeTransition(transaction);
            }
            pg.removeLocation(locationToRemove);
        }
    }


    private boolean getStateAndTransitions(NanoPromelaParser.StmtContext root, Set<String> locations, Set<PGTransition<String, String>> transitions) {
        //Basic case of recursion
        if (BaseCase(root, locations, transitions))
            return true;
        //recursion cases
        if (IfCase(root, locations, transitions))
            return true;
        if (DoCase(root, locations, transitions))
            return true;
        return SemicolonCase(root, locations, transitions);

    }

    private boolean DoCase(NanoPromelaParser.StmtContext root, Set<String> locations, Set<PGTransition<String, String>> transitions) {
        if (root.dostmt() == null)
            return false;
        String doLocation = root.dostmt().getText();
        locations.add(doLocation);

        for (NanoPromelaParser.OptionContext stmi : root.dostmt().option()) {
            getStateAndTransitions(stmi.stmt(), locations, transitions);
        }
        //help for the second Derivation
        for (String location : locations) {
            if (!location.equals("")) {
                Set<PGTransition<String, String>> toAdd = new HashSet<>();
                for (PGTransition<String, String> transition : transitions) {
                    if (transition.getFrom().equals(location)) {
                        String to = "";
                        if ("".equals(transition.getTo())) {
                            to = doLocation;
                        } else {
                            to = transition.getTo() + ";" + doLocation;
                        }
                        String from = location + ";" + doLocation;
                        toAdd.add(new PGTransition<>(
                                from,
                                transition.getCondition(),
                                transition.getAction(),
                                to
                        ));
                    }
                }
                transitions.addAll(toAdd);
            }
        }

        //third rule
        StringBuilder exitCondition = new StringBuilder();
        for (NanoPromelaParser.OptionContext stmi : root.dostmt().option()) {
            String check=stmi.boolexpr().getText();
            if (!exitCondition.toString().contains(stmi.boolexpr().getText()) && !stmi.boolexpr().getText().contains("true")) {
                if (!exitCondition.toString().equals(""))
                    exitCondition.append("&&");
                exitCondition.append("!").append("("+stmi.boolexpr().getText()+")");
            }
        }
        if(exitCondition.toString().equals(""))
            exitCondition.append("!((true)||(true))");
        transitions.add(new PGTransition<>(
                doLocation,
                exitCondition.toString(),
                "",
                ""
        ));

        //first and second rule

        for (NanoPromelaParser.OptionContext stmi : root.dostmt().option()) {
            String from = stmi.stmt().getText();
            //can't change the transition in foreach- java restriction
            Set<PGTransition<String, String>> toAdd = new HashSet<>();
            for (PGTransition<String, String> transition : transitions) {
                if (transition.getFrom().equals(from)) {
                    String condition = transition.getCondition();
                    String to = "";
                    //if to=ExitLocation -> second rule
                    if (!transition.getTo().equals(""))
                        to = transition.getTo() + ";";
                    to += doLocation;
                    toAdd.add(new PGTransition<>(
                            from + ";" + doLocation,
                            condition,
                            transition.getAction(),
                            to
                    ));
                    locations.add(from + ";" + doLocation);
                    locations.add(to);
                }
            }
            transitions.addAll(toAdd);
        }
        Set<PGTransition<String, String>> toAdd = new HashSet<>();
        for (PGTransition<String, String> transaction : transitions) {
            for (NanoPromelaParser.OptionContext stmi : root.dostmt().option()) {
                if (transaction.getFrom().equals(stmi.stmt().getText() + ";" + doLocation)) {
                    toAdd.add(new PGTransition<>(
                            doLocation,
                            "("+stmi.boolexpr().getText()+")" + "&&" + "("+transaction.getCondition()+")",
                            transaction.getAction(),
                            transaction.getTo()
                    ));
                }
            }

        }
        transitions.addAll(toAdd);
        Set<String> locationToRemove = new HashSet<>();
        for (String location : locations) {
            if (!location.contains(doLocation) && !location.equals(""))
                locationToRemove.add(location);
        }
        locations.removeAll(locationToRemove);

        for (PGTransition<String,String> transaction:transitions) {
            if(transaction.getCondition().equals("(true)&&(true)"))
                transaction.setCondition("(true)");
        }
        return true;
    }

    private boolean IfCase(NanoPromelaParser.StmtContext root, Set<String> locations, Set<PGTransition<String, String>> transitions) {
        if (root.ifstmt() == null)
            return false;
        String locationIf = root.ifstmt().getText();
        locations.add(locationIf);
        for (NanoPromelaParser.OptionContext stmi : root.ifstmt().option()) {
            getStateAndTransitions(stmi.stmt(), locations, transitions);
        }
        for (NanoPromelaParser.OptionContext stmi : root.ifstmt().option()) {
            String from = stmi.stmt().getText();
            //can't change the transition in foreach- java restriction
            Set<PGTransition<String, String>> toAdd = new HashSet<>();
            for (PGTransition<String, String> transition : transitions) {
                if (transition.getFrom().equals(from)) {
                    StringBuilder condition =new StringBuilder();
                    if(!stmi.boolexpr().getText().contains("true"))
                        condition.append("(").append(stmi.boolexpr().getText()).append(")");
                    if(!transition.getCondition().contains("true")){
                        if(!condition.toString().equals(""))
                            condition.append("&&");
                        condition.append("(").append(transition.getCondition()).append(")");
                    }
                    toAdd.add(new PGTransition<>(
                            locationIf,
                            condition.toString(),
                            transition.getAction(),
                            transition.getTo()
                    ));
                }
            }
            transitions.addAll(toAdd);
        }
        return true;
    }

    private boolean SemicolonCase(NanoPromelaParser.StmtContext root, Set<String> locations, Set<PGTransition<String, String>> transitions) {
        Set<String> subsRight = new HashSet<>();
        getStateAndTransitions(root.stmt(1), subsRight, transitions);
        locations.addAll(subsRight);
        //left subs
        Set<String> subsLeft = new HashSet<>();
        //remove the exit location
        getStateAndTransitions(root.stmt(0), subsLeft, transitions);
        subsLeft.remove("");
        for (String sub : subsLeft) {
            String stmt2 = root.stmt(1).getText();
            locations.add(sub + ";" + stmt2);
            //can't change the transition in foreach- java restriction
            Set<PGTransition<String, String>> toAdd = new HashSet<>();
            Set<PGTransition<String, String>> transitionToRemove = new HashSet<>();
            for (PGTransition<String, String> transition : transitions) {
                if (transition.getFrom().equals(sub)) {
                    switch (transition.getTo()) {
                        case "":
                            toAdd.add(new PGTransition<>(sub + ";" + stmt2,
                                    transition.getCondition(),
                                    transition.getAction(),
                                    stmt2));
                            transitionToRemove.remove(transition);
                            break;
                        default:
                            toAdd.add(new PGTransition<>(sub + ";" + stmt2,
                                    transition.getCondition(),
                                    transition.getAction(),
                                    transition.getTo() + ";" + stmt2));
                    }
                }
            }
            transitions.removeAll(transitionToRemove);
            transitions.addAll(toAdd);
        }
        return true;
    }

    private boolean BaseCase(NanoPromelaParser.StmtContext root, Set<String> locations, Set<PGTransition<String, String>> transitions) {
        if (root.skipstmt() != null || root.atomicstmt() != null || root.chanreadstmt() != null || root.chanwritestmt() != null
                || root.assstmt() != null) {
            String from = root.getText();
            String to = "";
            String Condition = "true";
            String action = "";
            if (root.skipstmt() != null)
                action = "skip";
            else
                action = root.getText();
            locations.addAll(Arrays.asList(from, to));
            transitions.add(new PGTransition<String, String>(from, Condition, action, to));
            return true;
        }
        return false;
    }


    /**
     * Creates a transition system from a transition system and an automaton.
     *
     * @param <Sts>  Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    The automaton.
     * @return The product of {@code ts} with {@code aut}.
     */
    public <Sts, Saut, A, P> TransitionSystem<Pair<Sts, Saut>, A, Saut> product(TransitionSystem<Sts, A, P> ts,
                                                                                Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Verify that a system satisfies an omega regular property.
     *
     * @param <S>    Type of states in the transition system.
     * @param <Saut> Type of states in the automaton.
     * @param <A>    Type of actions in the transition system.
     * @param <P>    Type of atomic propositions in the transition system, which is
     *               also the type of the automaton alphabet.
     * @param ts     The transition system.
     * @param aut    A Büchi automaton for the words that do not satisfy the
     *               property.
     * @return A VerificationSucceeded object or a VerificationFailed object
     * with a counterexample.
     */
    public <S, A, P, Saut> VerificationResult<S> verifyAnOmegaRegularProperty(TransitionSystem<S, A, P> ts,
                                                                              Automaton<Saut, P> aut) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * Translation of Linear Temporal Logic (LTL) formula to a Nondeterministic
     * Büchi Automaton (NBA).
     *
     * @param <L> Type of resultant automaton transition alphabet
     * @param ltl The LTL formula represented as a parse-tree.
     * @return An automaton A such that L_\omega(A)=Words(ltl)
     */
    public <L> Automaton<?, L> LTL2NBA(LTL<L> ltl) {
        throw new java.lang.UnsupportedOperationException();
    }

    /**
     * A translation of a Generalized Büchi Automaton (GNBA) to a
     * Nondeterministic Büchi Automaton (NBA).
     *
     * @param <L>    Type of resultant automaton transition alphabet
     * @param mulAut An automaton with a set of accepting states (colors).
     * @return An equivalent automaton with a single set of accepting states.
     */
    public <L> Automaton<?, L> GNBA2NBA(MultiColorAutomaton<?, L> mulAut) {
        throw new java.lang.UnsupportedOperationException();
    }


}
