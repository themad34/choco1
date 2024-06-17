package choco1;



import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.iterators.DisposableValueIterator;

import gurobi.GRB;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;

public class LP_IPropagator extends Propagator<IntVar>{
	IntVar[] x;
	IntVar[][] ad;
	int I,J;
	int counter=0;
	GRBEnv env;
	GRBModel model;
	GRBVar[][] Xij;
	

	
	class change{
		GRBVar var;
		double lb,ub;
		change(GRBVar var,double lb,double ub){
			this.var=var;
			this.lb=lb;
			this.ub=ub;
			
		}
	}
	

	

    public LP_IPropagator(IntVar[] X, IntVar[]... ad) {
        super(X,PropagatorPriority.BINARY,true);
        this.x = X;
        this.ad = ad;
        
     
        

        
	  	I = x.length;
	
	  	try {
	  		env = new GRBEnv(true);
	  		env.set(GRB.IntParam.LogToConsole, 0);
	  		env.start();
			model = new GRBModel(env);
			
			
			J=0;
		  	
		  	float epsilon=0;
		  	for(int i=0;i<I;i++) {
		  		J=Math.max(J,x[i].getUB());
		  		epsilon+=x[i].getDomainSize();
		  	}
		  	J+=1;
		  	epsilon=1/(epsilon+1);
		  	
		  	Xij = new GRBVar[I][J];
		  	GRBVar[][] Eij = new GRBVar[I][J];
		  	GRBLinExpr[] Sum_i = new GRBLinExpr[I];
		  	
		  	model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
		
		  	  	

		  	for(int i=0;i<I;i++) {
		  	

		  		Sum_i[i] = new GRBLinExpr();
		  		
		  		
		  		for(int j : x[i]) {

		  			
		  			Xij[i][j] = model.addVar(0.0, 1.0, 0.0, GRB.CONTINUOUS,"x_"+i+"_"+j);
		  			
		  			Eij[i][j] = model.addVar(0.0, GRB.INFINITY, 1.0, GRB.CONTINUOUS,"e_"+i+"_"+j);
		  			
		  			GRBLinExpr expr;
		  			expr = new GRBLinExpr();
		  			expr.addTerm(1.0, Xij[i][j]);
		  			expr.addTerm(1.0, Eij[i][j]);
		  			model.addConstr(expr, GRB.GREATER_EQUAL, epsilon, "ep_"+i+"_"+j);
		  			
		  			Sum_i[i].addTerm(1.0,Xij[i][j]);
		  		}
		  		model.addConstr(Sum_i[i], GRB.EQUAL, 1.0, "sum_i_"+i);
		  	}
		  	

		  	GRBLinExpr[] Sum_j = new GRBLinExpr[J];
		  	for (IntVar[] XX : ad) {
		  		for (int j=0;j<J;j++) {
		  			Sum_j[j] = new GRBLinExpr();
		  			
		  			for(int i=0;i<I;i++) {
		  				for(IntVar xad : XX) {
		  					if(xad==x[i]) {
		  						if (x[i].contains(j)) {
		  			
		  							Sum_j[j].addTerm(1.0, Xij[i][j]);
		  						}
		  						
		  					}
		  				}
		  			}
		  			model.addConstr(Sum_j[j], GRB.LESS_EQUAL, 1.0, "sum_j_"+j);
		  		}
		  	}
			
			
		} catch (GRBException e) {
			System.out.println("Error code: "+e.getErrorCode()+". "+e.getMessage());
		}
	  	
       
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
    	//System.out.println("propagate");
    	try {
 
    		
		  	model.optimize();
		  	
		  
		  	
		  	int status = model.get(GRB.IntAttr.Status);
		 
		  	if(status == 2){
	  			for(int i=0;i<I;i++) {
	  				for(int j=0;j<J;j++) {
	  					if(Xij[i][j]!=null) {
	  						if(Xij[i][j].get(GRB.DoubleAttr.X)==0.0) {
	  						   	
	  						x[i].removeValue(j, null);
	  						Xij[i][j].set(GRB.DoubleAttr.UB, 0.0);
	  						
	  						
	  					}
//	  					
//	  					if(Xij[i][j].get(GRB.DoubleAttr.X)==1.0 && !x[i].isInstantiated()) {
//  							System.out.println(">>>"+Xij[i][j].get(GRB.StringAttr.VarName));
//  							//x[i].instantiateTo(j, null);
//  						
//  						}
	  					}
	  				}
	  			}
	  		
	  	
		  	}
		  	else {
	
		  	
		  		throw new ContradictionException();
		  	}
		  	
		  
		 

    	} catch (GRBException e) {
    		System.out.println("Error code: "+e.getErrorCode()+". "+e.getMessage());
    	}
    }
    
    public void propagate(int varIdx, int evtmask) throws ContradictionException {
    	//System.out.println("propagate : "+x[varIdx]);
    	try {
    		
    		
    		for(int i=0;i<I;i++) {
    			DisposableValueIterator vit = x[i].getValueIterator(true);
    			
    			for(int j=0;j<J;j++) {
    				if(Xij[i][j]!=null) Xij[i][j].set(GRB.DoubleAttr.UB, 0.0);
    			}
    			
    			
    			while(vit.hasNext()){
    				int v = vit.next();
    				Xij[i][v].set(GRB.DoubleAttr.UB, 1.0);
    			}
    			vit.dispose();
    		}
    		
    			
    
    		

		  	model.optimize();
		  	
	 
		  	
		  	int status = model.get(GRB.IntAttr.Status);
		 
		  	if(status == 2){
	  			for(int i=0;i<I;i++) {
	  				for(int j=0;j<J;j++) {
	  					if(Xij[i][j]!=null ) {
	  						if(Xij[i][j].get(GRB.DoubleAttr.X)==0.0) {
	  					
		  					
		  						
		  						x[i].removeValue(j, null);
		  						Xij[i][j].set(GRB.DoubleAttr.UB, 0.0);
		  						/////////////////////////////////////::
		  						///////////////////////////////////////:::
		  						///////////////////////////////////////////
	  				
	  						}
//	  						if(Xij[i][j].get(GRB.DoubleAttr.X)==1.0 && !x[i].isInstantiated()) {
//	  							System.out.println(">>>"+Xij[i][j].get(GRB.StringAttr.VarName));
//	  							//x[i].instantiateTo(j, null);
//	  						
//	  						}
	  					}
	  				}
	  			}
	  			
	  			
	
		  	}
		  	else {
		  		

		  		throw new ContradictionException();
		  	}
		  	
		

    	} catch (GRBException e) {
    		System.out.println("Error code: "+e.getErrorCode()+". "+e.getMessage());
    	}
    }
    
    
    
    

    public void printLPModel() {
    	try {
    		
    		System.out.println("-----");
    	Variable[] csp = x[0].getModel().getVars();
    	for(int i=0;i<Xij.length;i++) {
    		System.out.println(csp[i]);
    		System.out.print("xij["+i+"] ");
    		for(int j=0;j<Xij[i].length;j++) {
    			if(Xij[i][j]!=null) System.out.print("["+j+"] = {"
    					+(int)Xij[i][j].get(GRB.DoubleAttr.LB)+","
    					+(int)Xij[i][j].get(GRB.DoubleAttr.UB)+"} "
    					);
    			
    		}
    		System.out.print("\n");
    	}
    	}
    	catch (GRBException e) {
    		
    	}
    	
    	
    }
    
    
    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.instantiation();
 
    	
    }

    @Override
    public ESat isEntailed() {
 
            return ESat.UNDEFINED;
    }
}