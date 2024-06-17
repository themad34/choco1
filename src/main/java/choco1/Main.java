package choco1;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;
import java.util.Vector;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.search.loop.monitors.IMonitorOpenNode;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;



public class Main {
	

	public static LP_IPropagator iprop;
	
	
	public static int gc=0;
	public static void nodeCounter(Solver solver) {

		gc=0;
		solver.plugMonitor(new IMonitorOpenNode() {
			@Override
			public void beforeOpenNode() {
				System.out.print(++gc+"\r");
				System.out.flush();
			}
		});
	}
	
	

	public static List<List<Integer>> parseLs(String s, int n){
		List<List<Integer>> latin = new ArrayList<List<Integer>>(n);
        for (int i = 0; i < n; ++i) {
            List<Integer> inner = new ArrayList<Integer>(n);
            for (int j = 0; j < n; ++j) {
                inner.add(j);
            }
            latin.add(inner);
        }
        
        s = s.replace("\n","");
        String v[] = s.split(" ");
        
        for(int i=0;i<n;i++) {
        	for(int j=0;j<n;j++) {
        		latin.get(i).set(j, Integer.parseInt(v[i*n+j]));
        	}
        }
        return latin;
	}
	
	public static List<List<Integer>> initialize(List<List<Integer>> L, int N){
		for (int i = 0; i < N; ++i) {
            List<Integer> inner = new ArrayList<Integer>(N);
            for (int j = 0; j < N; ++j) {
                inner.add(0);
            }
            L.add(inner);
        }
		
		return L;
	}
	
	public static boolean checkLatinSquare(List<List<Integer>> L) {
		int N=L.size();
		for(int i=0;i<N;i++) {
			for(int j=0;j<N;j++) {
				if(L.get(i).get(j)!=0) {
					for(int a=0;a<N;a++) {
						for(int b=0;b<N;b++) {
							if(a==i && j!=b && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(a!=i && j==b && L.get(i).get(j)==L.get(a).get(b)) return false;
						}
					}
				}

			}
		}
		
		
		return true;
	}
	
	public static List<List<Integer>> generate(int N, double fill){
		List<List<Integer>> L = new ArrayList<List<Integer>>(N);
		initialize(L,N);
		Random random = new Random();
		
		int limit=(int) Math.ceil(N*N*fill);
		
		
		
		
		Vector<int[]> v = new Vector<int[]>(N);
		for(int i=0;i<N;i++) {
			for(int j=0;j<N;j++) {
				v.add(new int[] {i,j});
			}
		}
		
		int[] a;
		int r,t;
		for(int c=0;c<limit;c++) {
			r = random.nextInt(v.size());
			a = v.get(r);
			v.remove(r);
			t=0;
			do {
				L.get(a[0]).set(a[1],random.nextInt(N)+1);
				t++;
			} while(!checkLatinSquare(L) && t<N*N);
			
			if(t==N*N) return generate(N,fill);
		}
	
		return L;
	}
	
	public static boolean checkLatinSquare2(List<List<Integer>> L) {
		int N=L.size();
		for(int i=0;i<N;i++) {
			for(int j=0;j<N;j++) {
				if(L.get(i).get(j)!=0) {
					for(int a=0;a<N;a++) {
						for(int b=0;b<N;b++) {
							if(a==i && j!=b && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(a!=i && j==b && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(a>0 && a-1==i && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(a<N-1 && a+1==i && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(b>0 && b-1==j && L.get(i).get(j)==L.get(a).get(b)) return false;
							if(b<N-1 && b+1==j && L.get(i).get(j)==L.get(a).get(b)) return false;
						}
					}
				}

			}
		}
		
		
		return true;
	}
	
	public static List<List<Integer>> generate2(int N, double fill){
		List<List<Integer>> L = new ArrayList<List<Integer>>(N);
		initialize(L,N);
		Random random = new Random();
		
		int limit=(int) Math.ceil(N*N*fill);
		
		
		
		
		Vector<int[]> v = new Vector<int[]>(N);
		for(int i=0;i<N;i++) {
			for(int j=0;j<N;j++) {
				v.add(new int[] {i,j});
			}
		}
		
		int[] a;
		int r,t;
		for(int c=0;c<limit;c++) {
			r = random.nextInt(v.size());
			a = v.get(r);
			v.remove(r);
			t=0;
			do {
				L.get(a[0]).set(a[1],random.nextInt(N+N)+1);
				t++;
			} while(!checkLatinSquare2(L) && t<N*N);
			//dead end
			if(t==N*N) return generate2(N,fill);
		}
	
		return L;
	}
	
	
	public static boolean trivialCheck(List<List<Integer>> ls, int n) {
		Model model = new Model();
		Solver solver = model.getSolver();
		
		IntVar[] vars = new  IntVar[n*n];
		for(int i=0;i<n;i++) {
			for(int j=0;j<n;j++) {
				if(ls.get(i).get(j)==0) {
					vars[i*n+j] = model.intVar("x_"+i+"_"+j,1,n);
				}
				else {
					vars[i*n+j] = model.intVar("x_"+i+"_"+j,ls.get(i).get(j));
				}
			}
		}

		IntVar[][] AD = new IntVar[n+n][n];

		
		for(int i=0;i<n;i++) {
			for(int j=0;j<n;j++) {
				AD[i][j] = vars[i*n+j];
				AD[n+j][i] = vars[i*n+j];
			}
		}
		
		for(IntVar[] ad : AD) {
			model.allDifferent(ad,"AC").post();
			
		}
		
		solver.solve();
		if (solver.getNodeCount()==0) return false;
		return true;
		
	}
	
	public static void printMatrix(List<List<Integer>> ls) {
		for(List<Integer> row : ls) {
			for(Integer x : row) {
				//System.out.print(x+" ");
				System.out.printf("%4s", x);
			}
			System.out.println();
		}
		System.out.println();
	}
	
	///////////////////////////////////////////////////
	///////////////////////////////////////////////////
	///////////////////////////////////////////////////
	
	
	
	public static void testLatinSquare(int n,double fill, int rep, int limit) {
		
		int k=n+n;
		int count=1;

		int nb_sat=0;
		int nb_unsat=0;
		int nb_unsat2=0;
		int nb_toolong=0;

		
		
		int tests[] = {0,4,2,1,7};
		int nb_tests=tests.length;
		
		int[] Nodes = new int[nb_tests];
		float[] Times = new float[nb_tests];
		int[] Backtracks = new int[nb_tests];
		int[] Solutions = new int[nb_tests];
		
		String[] Names = {
				"AC",			//0
				"LP",			//1
				"1LP+AC",		//2
				"test LP inc",	//3
				"AC cp17",		//4
				"LP lexico",	//5
				"AC lexico",	//6			
				"SAC",			//7
		
		};
		
	
		for(int i=0;i<nb_tests;i++) {
			Nodes[i]=0;
			Times[i]=0;
			Backtracks[i]=0;
			Solutions[i]=0;
			
		}
		
		Model model;
		Solver solver;
		
		
		for(int r=1;r<=rep;count++) {
		
			System.out.println("\n=============== Instance n°"+count+" ===============");
			//long start = System.nanoTime();
			
			List<List<Integer>> ls;
			
			ls = generate(n,fill);
			while(trivialCheck(ls,n)==false) {
				nb_unsat++;
				ls = generate(n,fill);
			}
			
			//long finish = System.nanoTime();
			//printMatrix(ls);
			
			
	
			
			
			for(int t=0;t<nb_tests;t++) {
				
				model = new Model();
				solver = model.getSolver();
				
				IntVar[] vars = new  IntVar[n*n];
				for(int i=0;i<n;i++) {
					for(int j=0;j<n;j++) {
						if(ls.get(i).get(j)==0) {
							vars[i*n+j] = model.intVar("x_"+i+"_"+j,1,n);
						}
						else {
							vars[i*n+j] = model.intVar("x_"+i+"_"+j,ls.get(i).get(j));
						}
					}
				}
		
				IntVar[][] AD = new IntVar[k][n];
	
				
				for(int i=0;i<n;i++) {
					for(int j=0;j<n;j++) {
						AD[i][j] = vars[i*n+j];
						AD[n+j][i] = vars[i*n+j];
					}
				}
				
				
				
				switch(tests[t]) {
				
				case 0:
					System.out.println("\n------------ AC (choco) ------------");
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
						
					}
					

					break;
				
					
				case 1:
					System.out.println("\n------------  LP    ------------");
				
					
					Constraint c14 = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(c14);
					
					break;
					
				case 3:
					System.out.println("\n------------- test incp -------------");
				
					iprop = new LP_IPropagator(vars,AD);
					
					Constraint c1 = new Constraint("ad",iprop);
					
					model.post(c1);
					
					//solver.setSearch(Search.inputOrderLBSearch(vars));
					
					break;
					
				
				case 4:
					System.out.println("\n------------ AC  (cp17) ------------");
					for(IntVar[] ad : AD) {
						model.post(new Constraint(" ",new LPF(ad)));
					}
					
					break;
					
				case 2:
					System.out.println("\n------------  1LP + AC  ------------");
					
					
				
					Constraint d = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(d);
					try {
						solver.propagate();
					} catch (ContradictionException e) {
						
					}
					model.unpost(d);
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
					}
					
			
					break;
					
					
				case 5:
					System.out.println("\n------------  LP lexico ------------");
				
					
					Constraint c5 = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(c5);
					
					solver.setSearch(Search.inputOrderLBSearch(vars));
					break;
									
				
				
					
				case 6:
					System.out.println("\n------------ AC lexico ------------");
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();	
					}
					solver.setSearch(Search.inputOrderLBSearch(vars));
		
					break;
					
				
					
				case 7:
					System.out.println("\n------------ SAC ------------");
			
				
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();	
					}
					
					solver.setPropagate(new SAC(vars));
			
					
					break;
					
			
				}
				
			
			
				solver.setSearch(Search.inputOrderLBSearch(vars));
				
			
				if(limit>0) solver.limitNode(limit);

				//nodeCounter(solver);
		
				
				
				//solver.showSolutions();
				//solver.findAllSolutions();
				//solver.showDecisions();
		
				solver.solve();
				//solver.printStatistics();
			

				if(solver.getSolutionCount()>0) {
					Nodes[t]+=solver.getNodeCount();
					Times[t]+=solver.getTimeCount();
					Backtracks[t]+=solver.getBackTrackCount();
					Solutions[t]+=solver.getSolutionCount();
	
				}
	
				

				System.out.println("Solutions: "+solver.getSolutionCount());
				
				//if(tests[t]==0 && solver.getSolutionCount()==0 && solver.getNodeCount()==0) nb_unsat++;
				System.out.println("Resolution time: "+solver.getTimeCount()+"s");
				System.out.println("Nodes: "+solver.getNodeCount());
				System.out.println("Backtracks: "+solver.getBackTrackCount());
				
				if(t==0) {
					if(solver.getSolutionCount()==0 && solver.getNodeCount()==limit) {
						nb_toolong++;
						r++;
					}
					if(solver.getSolutionCount()>0) {
						nb_sat++;
						r++;
					}
					if(solver.getSolutionCount()==0 && solver.getNodeCount()>0) {
						nb_unsat++;
						nb_unsat2++;
					}
				}
				
				if(t==1 && Solutions[0]!=Solutions[1]) {
					System.out.println("???");
					System.exit(0);
				}
				
				
				

			}
		
			
			
		}
		System.out.println("\nInstances of size "+n+"*"+n+" filled at "+fill*100+"%\n");
		
		System.out.println(nb_sat+" sat");	
		System.out.println(nb_unsat+" unsat ("+nb_unsat2+" non trivial)");
		if(limit>0) System.out.println(nb_toolong+" timeouts");


		System.out.printf("%n%-12s|%-8s|%-8s|%-14s%n"," Method"," Nodes","Bcktrcks"," Time (sec)");
		for(int f=0;f<nb_tests;f++) {
			
			System.out.printf("%-12s|%8s|%8s|%14s%n", Names[tests[f]],Nodes[f]/(rep-nb_toolong),Backtracks[f]/(rep-nb_toolong),Times[f]/(rep-nb_toolong));
		}
		
		
	}
	
	
	
	/*++++++++++++++++++++++++++++++++++++++++++++++
	 * +++++++++++++++++++++++++++++++++++++++++++++
	 * +++++++++++++++++++++++++++++++++++++++++++++*/
	
public static void printSolution(IntVar[] vars, int n) {
	for(int i=0;i<n;i++) {
		for(int j=0;j<n;j++) {
			System.out.printf("%4s",vars[i*n+j].getValue());
			
		}
		System.out.println();
	}
}


public static void printSudoku(IntVar[] vars, int n) {
	int sqrt = (int)Math.sqrt(n);
	for(int i=0;i<n;i++) {
		for(int j=0;j<n;j++) {
			System.out.printf("%4s",vars[i*n+j].getValue());
			if(j<n-1 && (j+1)%sqrt==0) 	System.out.print("│");
	
		}
		System.out.println();
		if(i<n-1 && (i+1)%sqrt==0) {
			for(int j=0;j<n;j++) {
				System.out.printf("%4s", "────");
				if(j<n-1 && (j+1)%sqrt==0) System.out.print("┼");

			}
			System.out.println();
		}
	}
}

public static void printSudoku(int[] vars, int n) {
	int sqrt = (int)Math.sqrt(n);
	for(int i=0;i<n;i++) {
		for(int j=0;j<n;j++) {
			System.out.printf("%4s",vars[i*n+j]);
			if(j<n-1 && (j+1)%sqrt==0) 	System.out.print("│");
	
		}
		System.out.println();
		if(i<n-1 && (i+1)%sqrt==0) {
			for(int j=0;j<n;j++) {
				System.out.printf("%4s", "────");
				if(j<n-1 && (j+1)%sqrt==0) System.out.print("┼");

			}
			System.out.println();
		}
	}
}


	
	
	
public static void testLatinSquare2(int n,double fill, int rep) {
		
		int k=n+n-2;
		int count=1;

		int nb_sat=0;
		int nb_unsat=0;
		int nb_unsat2=0;
		int nb_toolong=0;
		
		
		int tests[] = {1,0,4,2,3};
		int nb_tests=tests.length;
		
		int[] Nodes = new int[nb_tests];
		float[] Times = new float[nb_tests];
		int[] Backtracks = new int[nb_tests];
		int[] Solutions = new int[nb_tests];
		
		String[] Names = {
				"AC",		//0
				"LP",		//1
				"1LP+AC",	//2
				"SAC",		//3
				"AC cp17"	//4
			
				
		};
		
	
		for(int i=0;i<nb_tests;i++) {
			Nodes[i]=0;
			Times[i]=0;
			Backtracks[i]=0;
			Solutions[i]=0;
			
		}
		
		Model model;
		Solver solver;
		
		for(int r=1;r<=rep;count++) {
		
			System.out.println("\n=============== Instance n°"+count+" ===============");
			//long start = System.nanoTime();
			
			List<List<Integer>> ls;
			ls = generate2(n,fill);
			//printMatrix(ls);
			
			//long finish = System.nanoTime();
			
		//printMatrix(ls);
			
			

			
			for(int t=0;t<nb_tests;t++) {
	
				model = new Model();
				solver = model.getSolver();
				
				IntVar[] vars = new  IntVar[n*n];
				for(int i=0;i<n;i++) {
					for(int j=0;j<n;j++) {
						if(ls.get(i).get(j)==0) {
							vars[i*n+j] = model.intVar("x_"+i+"_"+j,1,n+n);
						}
						else {
							vars[i*n+j] = model.intVar("x_"+i+"_"+j,ls.get(i).get(j));
						}
					}
				}
		
				IntVar[][] AD = new IntVar[k][n+n];
	
				
				for(int i=0;i<n-1;i++) {
					for(int j=0;j<n-1;j++) {
						AD[i][j] = vars[i*n+j];
						AD[i][j+n] = vars[(i+1)*n+j];
						AD[n-1+j][i] = vars[i*n+j];
						AD[n-1+j][i+n] = vars[i*n+j+1];
					}
				}
				
				for(int i=0;i<n-1;i++) {
					AD[i][n-1]=vars[i*n+n-1];
					AD[i][n+n-1]=vars[(i+1)*n+n-1];
					
					AD[i+n-1][n-1]=vars[(n-1)*n+i];
					AD[i+n-1][n+n-1]=vars[(n-1)*n+i+1];
				}
				
	
				
				switch(tests[t]) {
				
				case 0:
					System.out.println("\n------------ AC (choco) ------------");
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
						
					}
					break;
				case 1:
					System.out.println("\n------------  LP  ------------");
					
					
					Constraint c = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(c);
					
					break;
				
				case 2:
					System.out.println("\n------------  1LP + AC  ------------");
					
					
					Constraint d = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(d);
					try {
						solver.propagate();
					} catch (ContradictionException e) {
						
					}
					model.unpost(d);
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
					}
					
					break;
					
				case 3:
					System.out.println("\n------------ SAC ------------");
			
				
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();	
					}
					
					solver.setPropagate(new SAC(vars));
			
					
					break;
					
				case 4:
					System.out.println("\n------------ AC  (cp17) ------------");
					for(IntVar[] ad : AD) {
						model.post(new Constraint(" ",new LPF(ad)));
					}
					
					break;
					
				}
			
				
				//solver.setSearch(Search.inputOrderLBSearch(vars));
				//solver.setSearch(Search.minDomLBSearch(vars));
				//solver.limitNode(2000);
				//nodeCounter(solver);
				//solver.showSolutions();
				//solver.findAllSolutions();
				//solver.showDecisions();
				solver.solve();
				//solver.printStatistics();
				

				
		
				
				
				if(solver.getSolutionCount()>0) {
					Nodes[t]+=solver.getNodeCount();
					Times[t]+=solver.getTimeCount();
					Backtracks[t]+=solver.getBackTrackCount();
					Solutions[t]+=solver.getSolutionCount();
	
				}
				
				System.out.println("Solutions: "+solver.getSolutionCount());
				
				//if(tests[t]==0 && solver.getSolutionCount()==0 && solver.getNodeCount()==0) nb_unsat++;
				System.out.println("Resolution time: "+solver.getTimeCount()+"s");
				System.out.println("Nodes: "+solver.getNodeCount());
				System.out.println("Backtracks: "+solver.getBackTrackCount());
				Boolean yes=false;
				if(t==0) {
					yes = false;
					if(solver.getSolutionCount()>0) {
						nb_sat++;
						r++;
						yes = true;
					}
					if(solver.getSolutionCount()==0 && solver.getNodeCount()>0) {
						nb_unsat++;
						nb_unsat2++;
					}
				}
				
				//if(t==0) printMatrix(ls);
				//if(solver.getSolutionCount()!=0) printSolution(vars,n);
				
				if(t==1 && yes && solver.getSolutionCount()==0) {
					Nodes[t]+=solver.getNodeCount()+18000;
					Times[t]+=solver.getTimeCount()*10;
					Backtracks[t]+=solver.getBackTrackCount();
					Solutions[t]+=solver.getSolutionCount();
				}
					
			}
		
			
			
		}

			System.out.println("\nInstances of size "+n+"*"+n+" filled at "+fill*100+"%\n");
			
			System.out.println(nb_sat+" sat");	
			System.out.println(nb_unsat+" unsat ("+nb_unsat2+" non trivial)");


			System.out.printf("%n%-12s|%-8s|%-8s|%-14s%n"," Method"," Nodes","Bcktrcks"," Time (sec)");
			for(int f=0;f<nb_tests;f++) {
				
				System.out.printf("%-12s|%8s|%8s|%14s%n", Names[tests[f]],Nodes[f]/(rep-nb_toolong),Backtracks[f]/(rep-nb_toolong),Times[f]/(rep-nb_toolong));
			}
			
		}
			
			
	
	
	
	
	
public static void testKillerSudoku() {
	int n=16;
	
																																																																																																																																																																																																																																																																																															
	int nb_sat=0;
	int nb_unsat=0;
	int nb_unsat2=0;
	
	int tests[] = {0,2,1,6};
	int nb_tests=tests.length;
	
	int[] Nodes = new int[nb_tests];
	float[] Times = new float[nb_tests];
	int[] Backtracks = new int[nb_tests];
	
	String[] Names = {
			"AC",		//0
			"LP",		//1
			"1LP+AC",	//2
			"LP incr",	//3
			"AC cp17",	//4
			"AC lexico",//5
			"SAC",		//6
			
			
	};
	

	for(int i=0;i<nb_tests;i++) {
		Nodes[i]=0;
		Times[i]=0;
		Backtracks[i]=0;
		
	}
	
	Model model;
	Solver solver;
	
	for(int in=0;in<100;in++) {
		Vector<int[]> cages = parseKS(in,"./killerSudoku-16x16");
		//Vector<int[]> cages = parseKS(in,"/home/marc-antoine/Seafile/Téléchargements/savilerow-1.9.1-linux/examples/killerSudoku");
			
			
			int k=n+n+n+cages.size();
	
	
			
		
	
		
				
			for(int t=0;t<nb_tests;t++) {
				
				model = new Model();
				solver = model.getSolver();
		

				IntVar[] vars = new  IntVar[n*n];
				for(int i=0;i<n;i++) {
					for(int j=0;j<n;j++) {
						vars[i*n+j] = model.intVar("x_"+i+"_"+j,1,n);
				
					}
				}
		
				IntVar[][] AD = new IntVar[k][];
				for(int i=0;i<3*n;i++) {
					AD[i] = new IntVar[n];
				}
				
				int sqrt = (int)Math.sqrt(n);
				for(int i=0;i<n;i++) {
					for(int j=0;j<n;j++) {
						AD[i][j] = vars[i*n+j];
						AD[n+j][i] = vars[i*n+j];
						AD[2*n+ (sqrt*(i/sqrt)) + (j/sqrt)][(i*sqrt)%n + j%sqrt] = vars[i*n+j];
					}
				}
				
				for(int i=0;i<cages.size();i++) {
					int[] cage = cages.get(i);
					int taille = (cage.length -1)/2;
					AD[3*n+i] = new IntVar[taille];
					
					IntVar[] sum = new IntVar[taille];
					
					int j=0;
					for(int l=1;l<cage.length;l+=2) {
						AD[3*n+i][j] = vars[cage[l]*n + cage[l+1]];
						sum[j] = vars[cage[l]*n + cage[l+1]];
						j++;
					}
				
					if(taille==1) model.arithm(vars[cage[1]*n+cage[2]], "=", cage[0]).post();
					if(taille==2) model.arithm(vars[cage[1]*n+cage[2]], "+",vars[cage[3]*n+cage[4]] , "=",cage[0]).post();
					if(taille>2) model.sum(sum, "=", cage[0]).post();
					
				}
				

				
				
				switch(tests[t]) {
				
				case 0:
					System.out.println("\n------------ AC (choco) ------------");
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
						
					}
					break;
				case 1:
					System.out.println("\n------------  LP    ------------");
					
					
					Constraint c = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(c);
					
					break;
					
				case 3:
					System.out.println("\n ------------ test incp ------------");
				
					
					Constraint c1 = new Constraint("ad", new LP_IPropagator(vars,AD));
					
					model.post(c1);
					
					break;
					
				
	
				case 2:
					System.out.println("\n------------  1LP + AC  ------------");
					
						
					Constraint d = new Constraint("ad",new LP_propagator(vars,AD));
					
					model.post(d);
					try {
						solver.propagate();
					} catch (ContradictionException e) {
						
					}
					model.unpost(d);
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();
					}
					
			
					break;
					
					
				case 4:
					System.out.println("\n------------ AC  (cp17) ------------");
					for(IntVar[] ad : AD) {
						model.post(new Constraint(" ",new LPF(ad)));
					}
					
					break;
					
				
	
					
					
				case 5:
					System.out.println("\n------------ AC lexico ------------");
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();	
					}
					solver.setSearch(Search.inputOrderLBSearch(vars));
		
					break;
					
					
					
				
					
				case 6:
					System.out.println("\n------------ SAC ------------");
			
				
					for(IntVar[] ad : AD) {
						model.allDifferent(ad,"AC").post();	
					}
					
					solver.setPropagate(new SAC(vars));
			
					
					break;
					
				}
					
				//nodeCounter(solver);
				//solver.limitTime("3600s");
//				if(t==0) solver.limitNode(30000);
//				else solver.limitNode(100000);
				//System.out.println(model);
				//solver.showSolutions();
				//solver.findAllSolutions();
				//solver.showDecisions();
				solver.solve();
				//solver.printStatistics();
	
				if(solver.getSolutionCount()>0) {
					Nodes[t]+=solver.getNodeCount();
					Times[t]+=solver.getTimeCount();
					Backtracks[t]+=solver.getBackTrackCount();
					//printSudoku(vars,n);
				}
				
				
				
	
				
				System.out.println("Solutions: "+solver.getSolutionCount());
				System.out.println("Resolution time: "+solver.getTimeCount()+"s");
				System.out.println("Nodes: "+solver.getNodeCount());
				System.out.println("Backtracks: "+solver.getBackTrackCount());
				
				if(t==0) {
					
					if(solver.getSolutionCount()>0) {
						nb_sat++;
					}
					if(solver.getSolutionCount()==0){
						t=100;
						nb_unsat++;
						if(solver.getNodeCount()>0) nb_unsat2++;
					}
				}
				

				
				
			
			}			
		}
	

	System.out.println(nb_sat+" sat");	
	System.out.println(nb_unsat+" unsat ("+nb_unsat2+" non trivial)");
	System.out.printf("%n%-12s|%-8s|%-8s|%-14s%n"," Method"," Nodes","Bcktrcks"," Time (sec)");
	for(int f=0;f<nb_tests;f++) {
		
		System.out.printf("%-12s|%8s|%8s|%14s%n", Names[tests[f]],Nodes[f]/nb_sat,Backtracks[f]/nb_sat,Times[f]/nb_sat);
	}
}


	public static Vector<int[]> parseKS(int n, String path) {
		
		Vector<int[]> cages = new Vector<int[]>();
		try {
			
			
			File dir = new File(path);
			Scanner scan;
			File f = dir.listFiles()[n];
			System.out.println(f);
			
			scan = new Scanner(f);
			String data = scan.nextLine();
			data = scan.nextLine();
			data = scan.nextLine();
			data = scan.nextLine();
			
			
			
			
			
			while(data.charAt(0)!=']') {
		
	
				data = data.split("\\[")[1];
				
			
				
				data = data.replaceAll("\\s", "");
				
				while(data != data.replaceAll(",0,0]","]")) {
					data = data.replaceAll(",0,0]", "]");
				}
				
				data = data.split("\\]")[0];
			
				
				String[] S = data.split(",");
				int[] cage = new int[S.length];
				cage[0] = Integer.parseInt(S[0]);
				for(int i=1;i<S.length;i++) {
					cage[i] = Integer.parseInt(S[i]) - 1;
				}
				cages.add(cage);
				
				
				data = scan.nextLine();
			}
				
			scan.close();
		
		
		}catch (FileNotFoundException e) {
			
		}
		
		
		return cages;
	}
		

	
	
	public static void main(String[] args) throws ContradictionException {
		
		//10 0.42
		//15 0.47
		//20 0.51  0.58
		//25 0.54
		//30 0.57
		
		
		
		testLatinSquare(25,0.55,100,-1);
		
		
		//testLatinSquare2(10,0.02,100);

		
		
		//testKillerSudoku();
		

	
		
		
	}
}
