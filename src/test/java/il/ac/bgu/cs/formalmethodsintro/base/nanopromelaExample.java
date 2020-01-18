package il.ac.bgu.cs.formalmethodsintro.base;

import java.io.IOException;
import java.util.Collections;
import java.util.Map;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaFileReader;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.OptionContext;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.StmtContext;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.PGTransition;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.formalmethodsintro.base.programgraph.ProgramGraph;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.GraphvizPainter;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class nanopromelaExample {
    FvmFacade f = FvmFacade.get();
    public void testPG2TS(StmtContext stmt) {
        ProgramGraph<String, String> pg = f.parseRoot(stmt);
        printPG(pg);
        TransitionSystem<Pair<String, Map<String, Object>>, String, String> ts = f.transitionSystemFromProgramGraph(pg, 
            Collections.singleton(new ParserBasedActDef()), 
            Collections.singleton(new ParserBasedCondDef()));
        TransitionsCheck.printTS(ts);
        System.out.println("\n\nDot\n");
        System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
    }

    public void testSubExpr(StmtContext stmt) {
        Sub sub = new SubParser().calcutalteSub(stmt);
        System.out.println(sub.toStringStrList());
        printPG(f.parseRoot(stmt));
    }
    
    public void printPG(ProgramGraph<?, ?> pg){
    	System.out.println(pg);
    	System.out.print("<");
    	for(Object s : pg.getLocations())
        	System.out.print(s.toString() + "\n");
    	System.out.println(">");
    	
    	System.out.print("<");
    	for(PGTransition<?, ?> t : pg.getTransitions())
            System.out.print(t.getFrom() + " ^&^ " + t.getCondition() + ":" + t.getAction() + " ^%^ " + t.getTo() + "\n");
        System.out.println(">");
        
		//System.out.println(GraphvizPainter.toStringPainter().makeDotCode(ts));
    }

    public void subnp(StmtContext stmt){
        if(stmt == null) return;
        System.out.println(stmt.getChildCount() + " " + stmt.depth() + " " + stmt.stmt().size());
        System.out.println(stmt.getText());
        if(stmt.ifstmt() != null)
            for(OptionContext o : stmt.ifstmt().option()){
                System.out.println(o.boolexpr().getText());
                subnp(o.stmt());
            }
        else if(stmt.dostmt() != null)
            for(OptionContext o : stmt.dostmt().option()){
                System.out.println(o.boolexpr().getText());
                subnp(o.stmt());
            }
        else for(StmtContext s : stmt.stmt()){
            subnp(s);
        }
    }

    @Test
    public void nanoPromela() {
        try {
            StmtContext stmt = NanoPromelaFileReader.pareseNanoPromelaFile(
                "src/main/java/il/ac/bgu/cs/formalmethodsintro/base/nanopromela/"+
                "tst5.np");        
            //subnp(stmt);
            testSubExpr(stmt);
            System.out.println("_|_|_|_|_");
            testPG2TS(stmt);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
