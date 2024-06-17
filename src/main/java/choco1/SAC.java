package choco1;

import org.chocosolver.solver.Solver;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.loop.propagate.PropagateBasic;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.iterators.DisposableValueIterator;
import org.chocosolver.util.objects.setDataStructures.iterable.IntIterableBitSet;
import org.chocosolver.util.objects.setDataStructures.iterable.IntIterableSet;


// https://drops.dagstuhl.de/opus/volltexte/2021/15304/pdf/LIPIcs-CP-2021-13.pdf

// choco 4.10.10  !!

public class SAC extends PropagateBasic {
	
	IntVar[] vars;

	public SAC(IntVar... vars) {

		this.vars = vars;
	}
	
	
	 @Override
	    public void execute(Solver solver) throws ContradictionException {   
	        super.execute(solver);  


	        boolean change = true;
	      
	        while(change){
	            change = false;

	            // For each pair Var/val:
	            for(IntVar v : vars){

	                if(v.isInstantiated())
	                    continue;

	                IntIterableSet valueSet = new IntIterableBitSet();
	                DisposableValueIterator vit = v.getValueIterator(true);

	                while(vit.hasNext()){
	                    int value = vit.next();
	                    solver.getModel().getEnvironment().worldPush();
	                    
	                    // Instantiate
	                    try{
	                        v.instantiateTo(value, null);
	                        // propagate
	                        solver.getEngine().propagate();
	                    }catch(ContradictionException cex)
	                    {
	                        solver.getEngine().flush();
	                        // This value is not Consistent
	                        change = true;
	                        valueSet.addAll(value);
	                        //System.out.println(cex);
	                    }
	                    // rewind
	                    solver.getModel().getEnvironment().worldPop();
	                    
	                }
	                vit.dispose();
	                
	                if(!valueSet.isEmpty()){

	                    v.removeValues(valueSet, null);
	                    
	                    solver.getEngine().propagate();   
	                    
	                }
	            }

	        }
	    }


}
