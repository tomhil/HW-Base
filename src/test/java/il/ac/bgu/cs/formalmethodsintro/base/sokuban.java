package il.ac.bgu.cs.formalmethodsintro.base;

import static java.util.Arrays.asList;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.GraphvizPainter;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class sokuban {
    private static FvmFacade f = FvmFacade.get();
    public TransitionSystem<Pair<Integer, Integer>, String, String> getUser(int i, int j, int square,
            List<Pair<Integer, Integer>> walls, List<Pair<Integer, Integer>> solutionBlocks) {
        return getTS(i, j, square, walls, solutionBlocks, true);
    }
    public TransitionSystem<Pair<Integer, Integer>, String, String> getBox(int i, int j, int square,
            List<Pair<Integer, Integer>> walls, List<Pair<Integer, Integer>> solutionBlocks) {
        return getTS(i, j, square, walls, solutionBlocks, false);
    }
    public TransitionSystem<Pair<Integer, Integer>, String, String> getTS(int i, int j, int square,
            List<Pair<Integer, Integer>> walls, List<Pair<Integer, Integer>> solutionBlocks, boolean user) {
		TransitionSystem<Pair<Integer, Integer>, String, String> ts1 = new TransitionSystem<>();
        ts1.setName(String.format("ts%d_%d",i,j));
        List<Pair<Integer,Integer>> legalStates = new LinkedList<>();
        for(int x1 = 0; x1 < square; x1++)
            for(int x2 = 0; x2 < square; x2++)
                legalStates.add(new Pair<>(x1, x2));
        ts1.addInitialState(new Pair<>(i, j));
        ts1.addAtomicPropositions("not_solved");
        for(Pair<Integer, Integer> p : legalStates)
            if(!solutionBlocks.contains(p))
                ts1.addToLabel(p, "not_solved");
        if(user)
            setTransUser(square, walls, ts1, legalStates);
        else{
            setTransBox(square, 1, walls, ts1, legalStates);
            transNothing(square, walls, ts1, legalStates);
        }
		return ts1;
    }

    //when other boxes move you will not move
    private void transNothing(int square, List<Pair<Integer, Integer>> walls,
            TransitionSystem<Pair<Integer, Integer>, String, String> ts, List<Pair<Integer, Integer>> legalStates) {
        for(Pair<Integer, Integer> p : legalStates){
            for(int i = 0; i < square; i++){
                for(int j = 0; j < square; j++){
                    if(walls.contains(p))//optimize
                        continue;
                    if(i != p.first && j != p.second && j != p.second-1)
                        ts.addTransition(new TSTransition<>(p, String.format("R(%d,%d)",i,j), p));
                    if(i != p.first && j != p.second && j != p.second+1)
                        ts.addTransition(new TSTransition<>(p, String.format("L(%d,%d)",i,j), p));
                    if(i != p.first && j != p.second && i != p.first+1)
                        ts.addTransition(new TSTransition<>(p, String.format("U(%d,%d)",i,j), p));
                    if(i != p.first && j != p.second && i != p.first-1)
                        ts.addTransition(new TSTransition<>(p, String.format("D(%d,%d)",i,j), p));
                }
            }
        }
    }

    private void setTransUser(int square, List<Pair<Integer, Integer>> walls,
            TransitionSystem<Pair<Integer, Integer>, String, String> ts, List<Pair<Integer, Integer>> legalStates) {
        for(Pair<Integer, Integer> p : legalStates){
            if(walls.contains(p))//optimize
                continue;
            addTransition(ts, walls, square, new TSTransition<>(p, String.format("R(%d,%d)",p.first, p.second), new Pair<>(p.first,p.second+1)));
            addTransition(ts, walls, square, new TSTransition<>(p, String.format("L(%d,%d)",p.first, p.second), new Pair<>(p.first,p.second-1)));
            addTransition(ts, walls, square, new TSTransition<>(p, String.format("U(%d,%d)",p.first, p.second), new Pair<>(p.first-1,p.second)));
            addTransition(ts, walls, square, new TSTransition<>(p, String.format("D(%d,%d)",p.first, p.second), new Pair<>(p.first+1,p.second)));
        }
    }

    private void setTransBox(int square, int diff, List<Pair<Integer, Integer>> walls,
            TransitionSystem<Pair<Integer, Integer>, String, String> ts, List<Pair<Integer, Integer>> legalStates) {
        for(Pair<Integer, Integer> p : legalStates){
            if(walls.contains(p))//optimize
                continue;
            addTransition(ts, walls, square, p.first, p.second-diff, new TSTransition<>(p, String.format("R(%d,%d)",p.first, p.second-diff), new Pair<>(p.first,p.second+1)));
            addTransition(ts, walls, square, p.first, p.second+diff, new TSTransition<>(p, String.format("L(%d,%d)",p.first, p.second+diff), new Pair<>(p.first,p.second-1)));
            addTransition(ts, walls, square, p.first+diff, p.second, new TSTransition<>(p, String.format("U(%d,%d)",p.first+diff, p.second), new Pair<>(p.first-1,p.second)));
            addTransition(ts, walls, square, p.first-diff, p.second, new TSTransition<>(p, String.format("D(%d,%d)",p.first-diff, p.second), new Pair<>(p.first+1,p.second)));
        }
    }
    
    private void addTransition(TransitionSystem<Pair<Integer, Integer>, String, String> ts,
            List<Pair<Integer, Integer>> walls, int square, Integer pushI, int pushJ, TSTransition<Pair<Integer, Integer>, String> t) {
        boolean ifcheck = pushI > -1 & pushI < square;//optimize
        ifcheck &= pushJ > -1 & pushJ < square;//optimize
        ifcheck &= !walls.contains(new Pair<>(pushI, pushJ));//optimize
        Pair<Integer, Integer> p = t.getTo();
        ifcheck &= p.first > -1 & p.first < square;
        ifcheck &= p.second > -1 & p.second < square;
        ifcheck &= !walls.contains(p);
        if(ifcheck)
            ts.addTransition(t);
    }

    private void addTransition(TransitionSystem<Pair<Integer, Integer>, String, String> ts,
            List<Pair<Integer, Integer>> walls, int square, TSTransition<Pair<Integer, Integer>, String> t) {
        boolean ifcheck = true;
        Pair<Integer, Integer> p = t.getTo();
        ifcheck &= p.first > -1 & p.first < square;
        ifcheck &= p.second > -1 & p.second < square;
        ifcheck &= !walls.contains(p);
        if(ifcheck)
            ts.addTransition(t);
    }

    TransitionSystem interleaveAll(Set<String> H, TransitionSystem<Pair<Integer, Integer>, String, String>... TS) {
        TransitionSystem X = TS[0];
        for(int i = 1; i < TS.length; i++){
            System.out.println("merge"+i);
            System.out.println(X);
            X = f.interleave(X, TS[i]);
        }
        return X;
    }

    //this is small sanity test
    @Test
    public void sokubanTest(){
        int square = 5;
        List<Pair<Integer, Integer>> solutionBlocks = asList(new Pair<>(2,2));
        List<Pair<Integer, Integer>> walls = getWalls(square);
        TransitionSystem<Pair<Integer, Integer>, String, String> ts = getBox(2, 2, square, walls, solutionBlocks);
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
        //System.out.println(ts.toString());
    }

    //@Test
    public void sokubanTestInterleave() {
        int square = 7;
        //new Pair<>(2,2), new Pair<>(3,3), new Pair<>(5,3), new Pair<>(5,4), new Pair<>(6,4)
        List<Pair<Integer, Integer>> solutionBlocks = asList(new Pair<>(1,1), new Pair<>(2,2), new Pair<>(4,2), new Pair<>(4,3), new Pair<>(5,3));
        List<Pair<Integer, Integer>> walls = getWalls(square);
        //indexs in test are from 1-7 here it from 0-6
        TransitionSystem<Pair<Integer, Integer>, String, String> ts1 = getBox(2, 1, square, walls, solutionBlocks);
        TransitionSystem<Pair<Integer, Integer>, String, String> ts2 = getBox(2, 2, square, walls, solutionBlocks);
        TransitionSystem<Pair<Integer, Integer>, String, String> ts3 = getBox(2, 4, square, walls, solutionBlocks);
        TransitionSystem<Pair<Integer, Integer>, String, String> ts4 = getBox(3, 4, square, walls, solutionBlocks);
        TransitionSystem<Pair<Integer, Integer>, String, String> ts5 = getBox(5, 3, square, walls, solutionBlocks);
        TransitionSystem<Pair<Integer, Integer>, String, String> tsuser = getUser(1, 2, square, walls, solutionBlocks);
        Set<String> H = ts1.getActions();
        System.out.println(interleaveAll(H ,ts1, ts2, ts3, ts4, ts5, tsuser).toString());
        //System.out.println(GraphvizPainter.toStringPainter().makeDotCode(interleaveAll(H ,ts1, ts2, ts3, ts4, ts5, tsuser)));
    }
    private List<Pair<Integer, Integer>> getWalls(int square) {
        List<Pair<Integer, Integer>> walls = new LinkedList<>();
        for(int x1 = 0; x1 < square; x1++)
            walls.add(new Pair<>(x1, 0));
        for(int x1 = 0; x1 < square; x1++)
            walls.add(new Pair<>(x1, square-1));        
        for(int x1 = 0; x1 < square; x1++)
            walls.add(new Pair<>(0, x1));
        for(int x1 = 0; x1 < square; x1++)
            walls.add(new Pair<>(square-1, x1));
        return walls;
    }
}

/*
*
* - problem with the ts - box can move into other box.
*   the bad run - user 1,2 -> 1,3, 1,3 -> 2,3, 2,3->2,2
                    box                        2,2->2,1 BOXES COLIDE
*   how to solve?
*       can edit (or create a new TS) the ts states and transition to remove the illegal states. or add 'bad' label to them
*       so a program that will analyze it will know which state to use(that are not bad).
*/
