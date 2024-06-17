package choco1;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import gurobi.*;

public class LPF extends Propagator<IntVar>{
	IntVar[] ad;
	int I,J;

    public LPF(IntVar[] ad) {
        super(ad);
        this.ad = ad;
         	
	  	I = ad.length;
        
       
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
    	
    	try {
    	GRBEnv env = new GRBEnv(true);
    	env.set(GRB.IntParam.LogToConsole, 0);
    	env.set("logFile", "lp.log");
    	env.start();
    	
    	GRBModel model = new GRBModel(env);
    	
	  	
	 
	  	J=0;
	  	
	  	float epsilon=0;
	  	for(int i=0;i<I;i++) {
	  		J=Math.max(J,ad[i].getUB());
	  		epsilon+=ad[i].getDomainSize();
	  	}
	  	J+=1;
	  	epsilon=1/(epsilon+1);
	  	
	  	GRBVar[][] Xij = new GRBVar[I][J];
	  	GRBVar[][] Eij = new GRBVar[I][J];
	  	GRBLinExpr[] Sum_i = new GRBLinExpr[I];
	  	
	  	model.set(GRB.IntAttr.ModelSense, GRB.MINIMIZE);
	
	  	  	

	  	for(int i=0;i<I;i++) {
	  	

	  		Sum_i[i] = new GRBLinExpr();
	  		
	  		
	  		for(int j : ad[i]) {

	  			
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
			  
  		for (int j=0;j<J;j++) {
  			Sum_j[j] = new GRBLinExpr();
  			for(int i=0;i<I;i++) {
  				if (ad[i].contains(j)) {
  					Sum_j[j].addTerm(1.0, Xij[i][j]);
  				}	
  			}
  			model.addConstr(Sum_j[j], GRB.LESS_EQUAL, 1.0, "sum_j_"+j);
  		}
		  	


	  	model.optimize();
	  	
	  	int status = model.get(GRB.IntAttr.Status);
	  	if(status == 2){
	  			for(int i=0;i<I;i++) {
	  				for(int j=0;j<J;j++) {
	  					if(Xij[i][j]!=null && Xij[i][j].get(GRB.DoubleAttr.X)==0.0) {
	  						
	  						ad[i].removeValue(j, null);
	  					}
	  				}
	  			}
	  	}
	  	else throw new ContradictionException();

	  

	  	model.dispose();
	  	env.dispose();

    	} catch (GRBException e) {
    		System.out.println("Error code: "+e.getErrorCode()+". "+e.getMessage());
    	}
    }

    @Override
    public ESat isEntailed() {
 
            return ESat.UNDEFINED;
    }
}