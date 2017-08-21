import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.StringTokenizer;

/** Class: TwoSAT_Satisfiability_Problem_SCC.java
 *  @author Yury Park
 *
 *  This class - 2-SAT problem solver.
 *
 *  The test data file format is as follows. In each instance, the number of variables and the number of clauses is the same,
 *  and this number is specified on the first line of the file. Each subsequent line specifies a clause via
 *  its two literals, with a number denoting the variable and a "-" sign denoting logical "not".
 *  For example, if the second line of a data file is "-16808 75250", it indicates the clause ¬x16808 v x75250.
 *
 *  This class will determine, for each data file, whether or not it is logically satisfiable.
 *  Since this problem reduces to the algorithm for finding the Strongly Connected Components (SCC) of a graph,
 *  this class uses that algorithm, resulting in asymtotically linear-time solution. For more details, see below:
 *  
 *  =======================================================================================
 *        A 2-SAT instance can be described using 2-CNF (Conjunctive Normal Form) as follows:
 *
 *        (x0 OR x1) AND (~x0 OR x2) AND (~x1 OR ~x2)
 *        The 2-SAT problem is to find a truth assignment to these variables that makes a formula of this
 *        type true: we must choose whether to make each of the variables true or false, so that every
 *        clause has at least one term that becomes true.
 *
 *        Aspvall, Plass & Tarjan (1979) found a simple linear time procedure for solving 2-SAT instances,
 *        based on the notion of strongly connected components. The algorithm is as follows:
 *        Create the inference graph G such that for each variable xi in the 2-SAT instance,
 *        xi and ~xi are vertices of the inference graph and are complements of each other.
 *        For each clause (u OR v), add the edges ~u -> v and ~v -> u to the inference graph G.
 *
 *        (Explanation: Recall from discrete math that ~u -> v (if NOT u, THEN v) is translated to u OR v.
 *        Same for ~v -> u, which is translated to v OR u.)
 *
 *        Process each of the strongly connected components S of G as follows:
 *        If x0 and ~x0 (i.e., a variable and its complement) belong to the same SCC,
 *        then stop and return false, the instance is unsatisfiable.
 *
 *		  Otherwise, keep going for all other variables and complements for every SCC.
 *		  Once we explored every SCC in this way (and haven't returned false in the process),
 *		  we know it's satisfiable. Return true.
 *  =======================================================================================
 */
public class TwoSAT_SCC {

	//needed for the SCC algorithm.
	private HashSet<Vertex> vertices;	//set of all vertices in the (assumed to be) directed graph.
	private ArrayList<Edge> edges;		//list of edges
	private Map<Integer, Vertex> vertexMap;	//maps an int value to a vertex.
	private String fileName;			//name of txt file to read data from in order to construct a graph
	private int t;		//finishing time in 1st pass of DFS-Loop
	private int n;		//the label no. of the biggest-labeled vertex
	private int m;		//the label no. of the smallest-labeled vertex
	private ArrayList<SCC> sccAL;	//ArrayList of SCC objects. Note SCC is an inner class in this file.
	private SCC scc;				//A global SCC object. Note SCC is an inner class in this file.
	private int numOfVars;			//total number of variables
	private int numOfClauses;		//total number of clauses
	
	//Below vars are not needed for this algorithm though may be useful in another context
//	private Vertex s;	//leader nodes in 2nd pass of DFS-Loop.
//	private int sccNumOfVertices;	//Keeps track of the number of nodes (components) in a single SCC object.
//	private int numOfLeaderVertices;
//	private ArrayList<Integer> topSccCount;	//Keeps track of the top 5 biggest SCC objects.
//	private int sccMinValue;		//Keeps track of the smallest SCC object in the topSccCount ArrayList.

	private static boolean debugOn;

	/**
	 * 2-arg constructor
	 * @param fileName
	 * @param debugMode
	 */
	public TwoSAT_SCC(String fileName, boolean debugMode) {
		debugOn = debugMode;
		this.fileName = fileName;
		this.t = 0;							//initialize the "finishing time" to zero.
		this.n = Integer.MIN_VALUE;			//initialize the label of the biggest vertex to min. value
		this.m = Integer.MAX_VALUE;			//initialize the label of the smallest vertex.
		this.sccAL = new ArrayList<SCC>();	//initialize an arraylist of SCC objects (mainly for debugging)
		this.scc = new SCC();				//initialize a new SCC object
		build();
	}

	/**
	 * Method: build
	 * Reads data re: directed graph from txt file and constructs the directed graph.
	 */
	private void build() {
		/* Initialize map, edges and vertices */
		this.vertexMap = new HashMap<Integer, Vertex>();	//This maps the label (integer) no. of a vertex to the vertex object
		this.edges = new ArrayList<Edge>();		//This keeps track of all the Edge objects in the graph.
		this.vertices = new HashSet<Vertex>();	//Keep track of all the vertices in the graph

		try {
			BufferedReader rd = new BufferedReader(new FileReader(new File(fileName)));

            //Read the first line, which contains info re: total no. of variables and total no. clauses
            String line = rd.readLine();

            StringTokenizer tokenizer = new StringTokenizer(line);
            this.numOfVars = Integer.parseInt(tokenizer.nextToken());

            /* Depending on the txt file, there may or may not be a 2nd entry in the first line. If there is,
             * then it contains the total no. of clauses. If there isn't, then total no. of vars = total no. of clauses. */
            if (tokenizer.hasMoreTokens()) this.numOfClauses = Integer.parseInt(tokenizer.nextToken());
            else this.numOfClauses = this.numOfVars;

            int index = 0;
            while (++index <= this.numOfClauses) {
            	line = rd.readLine();
                tokenizer = new StringTokenizer(line);
                int uLabel = Integer.parseInt(tokenizer.nextToken());
                int vLabel = Integer.parseInt(tokenizer.nextToken());

                int uLabelComplement = -uLabel;
                int vLabelComplement = -vLabel;

                /* Update the biggest vertex no. and the smallest vertex no. if appropriate. */
				this.n = Math.max(this.n, Math.max(Math.abs(uLabel),  Math.abs(vLabel)));
				this.m = Math.min(this.n, Math.min(Math.abs(uLabel) * -1,  Math.abs(vLabel) * -1));

				/* If vertexMap (HashMap) doesn't yet contain a Vertex object with the corresponding label, create one. */
				if(vertexMap.get(uLabel) == null) {
					vertexMap.put(uLabel, new Vertex(uLabel));
				}
				Vertex u = vertexMap.get(uLabel);

				/* Do the same for vLabel */
				if(vertexMap.get(vLabel) == null) {
					vertexMap.put(vLabel, new Vertex(vLabel));
				}
				Vertex v = vertexMap.get(vLabel);

				/* Do the same for the complements */
				if(vertexMap.get(uLabelComplement) == null) {
					vertexMap.put(uLabelComplement, new Vertex(uLabelComplement));
				}
				Vertex notU = vertexMap.get(uLabelComplement);

				if(vertexMap.get(vLabelComplement) == null) {
					vertexMap.put(vLabelComplement, new Vertex(vLabelComplement));
				}
				Vertex notV = vertexMap.get(vLabelComplement);

				/* Add all 4 vertices to the HashSet. This automatically takes care of any duplicates. */
				this.vertices.add(u);
				this.vertices.add(v);
				this.vertices.add(notU);
				this.vertices.add(notV);

				/* ATTENTION:
				 * A 2-SAT instance can be described using 2-CNF as follows:
				 *
				 * (x0 OR x1) AND (~x0 OR x2) AND (~x1 OR ~x2)
				 *
				 * The 2-SAT problem is to find a truth assignment to these variables that makes a formula of this
				 * type true: we must choose whether to make each of the variables true or false, so that every
				 * clause has at least one term that becomes true.
				 *
				 * Aspvall, Plass & Tarjan (1979) found a simple linear time procedure for solving 2-SAT instances,
				 * based on the notion of strongly connected components. The algorithm is as follows:
				 *
				 * Create the inference graph G such that for each variable xi in the 2-SAT instance,
				 * xi and ~xi are vertices of the inference graph. xi and ~xi are complements of each other.
				 *
				 * For each clause (u OR v), add the edges ~u -> v and ~v -> u to the inference graph G.
				 *
				 * (Why? Recall from discrete math that ~u -> v (if NOT u, THEN v) is translated to u OR v.
				 * Same for ~v -> u, which is translated to v OR u.)
				 *
				 * Process each of the strongly connected components S of G as follows:
				 * If x and ~x (i.e., a variable and its complement) belong to the same SCC,
				 * then stop and return false, the instance is unsatisfiable.
				 *
				 * Otherwise, keep going for all other variables and complements for every SCC.
				 * Once we explored every SCC in this way (and haven't returned false in the process),
				 * we know it's satisfiable. Return true.
				 *  */

				Edge edge = new Edge(notU, v);	//This directed edge goes from notU to v.
				this.edges.add(edge);

				/* Update the vertices' data fields with the edge. */
				notU.outgoingArrows.add(edge);
				v.incomingArrows.add(edge);

				Edge edge2 = new Edge(notV, u);	//This directed edge goes from notV to u.
				this.edges.add(edge2);
				notV.outgoingArrows.add(edge2);
				u.incomingArrows.add(edge2);
            }
            //end while
            rd.close();
            if (debugOn) {
            	System.out.println("All vertices in this graph and their directed arrows:");
				for(Vertex v : this.vertices) {
					System.out.println("vertex #" + v.lbl + ", outgoing arrows: " + v.toString2());
				}
				System.out.println("\nBiggest labeled vertex: " + this.n);
				System.out.println("Smallest labeled vertex: " + this.m + "\n");
            }
  		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		//end try/catch
	}
	//end private void build

	/**
	 * Method: Kosaraju
	 * 
	 * Algorithm for processing SCC.
	 */
	public void Kosaraju() {
		/* First, run dfsLoop on the graph with the arrows (edges) REVERSED. */
		dfsLoop(true);	//the parameter true means the arrows should be reversed
		System.out.println("dfsloop on reversedGraph done.\n");

		/* Re-assign all vertex labels with their finishingTime values. */
		this.vertexMap.clear();	//clear map because we need to re-assign the hashMap too.
		for(Vertex v : this.vertices) {
			v.lbl = v.finishingTime;
			this.vertexMap.put(v.lbl, v);
		}

		//testing
		if(debugOn) {
			for(Vertex v : this.vertices) {
				//lblBackup is such that we can later restore the original label to each vertex if needed
				System.out.printf("%s's label has been changed to %s.\n", v.lblBackup, v.lbl);
			}
		}

		System.out.println("reassigned all vertex labels with their finishingTime values.\n");

		/* Run dfsLoop again, this time with the reassigned vertex labels, and with the graph's arrows (edges)
		in their ORIGINAL DIRECTION. */
//		this.numOfLeaderVertices = 0;	//Initialize the no. of leader vertices before the 2nd dfsLoop invocation. UPDATE not needed
		dfsLoop(false);	//the parameter true means the arrows should NOT be reversed this time.

		/* Now that we're done with the 2nd dfsLoop invocation, restore label of each vertex from backup. */
		System.out.println("Now restoring the label of each vertex from backup..");
		this.vertexMap.clear();
		for(Vertex v : this.vertices) {
			v.lbl = v.lblBackup;
			this.vertexMap.put(v.lbl, v);
		}

		System.out.println("dfsLoop on orig. graph done.");

		boolean satisfiable = true;	//sentinel value initialized

		/* Process each of the strongly connected components S of G as follows:
		 * If x and ~x (i.e., a variable and its complement) belong to the same SCC,
		 * then stop and return false, the instance is unsatisfiable.
		 *
		 * Otherwise, keep going for all other variables and complements for every SCC.
		 * Once we explored every SCC in this way (and haven't returned false in the process),
		 * we know it's satisfiable. Return true.
		 *  */
		outerLoop:
		for(SCC sc : this.sccAL) {
			if (debugOn) System.out.println(sc);
			for (Vertex v : sc.sccGroup) {
				if (sc.contains(-1 * v.lbl)) {
					satisfiable = false;
					System.out.printf("Unsatisfiable SCC object found: %s.\n(%s and %s conflict!) Breaking out of outer loop...\n",
							sc, v.lbl, -1 * v.lbl);
					break outerLoop;
				}
			}
		}
		System.out.println(satisfiable ? "SATISFIABLE" : "UNSATISFIABLE"); //output solution
	}
	//end for i

	/**
	 * Method: dfsLoop
	 *         Invoked by Kosaraju() method.
	 * @param reverseGraph boolean value that determines whether to reverse the edges' directions in the graph.
	 */
	private void dfsLoop(boolean reverseGraph) {
		this.t = 0;	//initialize the "finishing time" value
//		this.s = null;	//initialize the "leader" value. UPDATE: Not needed.
		for (Vertex v : this.vertices) v.explored = false;	//Initialize all vertices to unexplored
		this.sccAL.clear();		//clear the ArrayList of SCC objects.

		//Initialize the ArrayList of top 5 SCC sizes to all zeroes. UPDATE: not needed for this algorithm.
//		this.topSccCount = new ArrayList<>(Arrays.asList(0, 0, 0, 0, 0));
//		this.sccMinValue = 0;

		/* Go thru each vertex label, from the biggest label down to the smallest label. */
		for(int i = this.n; i >= this.m; i--) {
			Vertex v_i = this.vertexMap.get(i);
			if(v_i == null) continue;	//if a Vertex object with the given label no. does not exist, then go on to next for loop iteration
			if(debugOn) System.out.println("Now checking vertex " + v_i.lbl);
			if(!v_i.explored) {	//if this vertex is unexplored...
				if(debugOn) System.out.println("Not explored! invoking dfs.....");
				this.scc = new SCC();
				dfs(v_i, reverseGraph);		//invoke dfs method!
				this.sccAL.add(this.scc);	//Add the SCC object to the ArrayList
			}
			else {
				if(debugOn) System.out.println("This label is explored. Moving on to the next vertex...");
			}
		}
		//end for

		/* If this is the first time this dfsLoop() method is being invoked by Kosaraju(), then it means
		 * this dfsLoop() method will be invoked a second time. Thus, we may need to update the max. and the min.
		 * label no. of vertices before the second pass. Why?
		 *
		 * Though the original label no.'s are assumed to be from 1 to whatever, what if our assumption is wrong?
		 * What if the label no's are originally something like: 0, 3, 4, 5, 10?
		 *
		 * Then there are a total of 5 vertices, but they range from 0 to 10. During the first dfsLoop() invocation,
		 * the for-loop looks at all the vertices from 10 all the way down to 0 (skipping over vertices that don't exist).
		 * Fine. But, once the labels are replaced (by the Kosaraju() method) by their respective finishing times (1 - 5),
		 * and dfsLoop() is invoked a 2nd time, then the label no. should go from 5 all the way down to 1 -- NOT from 10 to 0. */
		this.n = t;	 //t = the last finishing time = biggest vertex after vertex labels are replaced.
		this.m = 1;	 //the finishing times are from 1 to t, so the minimum vertex should always be 1 once vertex labels are replaced.
	}
	//end private void dfsLoop

	/**
	 * Method: dfs
	 *         Invoked by dfsLoop() method. Performs depth-first search starting with the given Vertex,
	 *         and keeps on exploring unexplored neighbors until it can't.
	 *         Assumes the graph is directed.
	 *         If reverseGraph variable is set to true, flips the arrows' directions before performing dfs.
	 * @param v_i given Vertex from where to begin the dfs search
	 * @param reverseGraph boolean variable that determines whether the arrows of the graph should be flipped.
	 */
	private void dfs(Vertex v_i, boolean reverseGraph) {
		v_i.explored = true;			//set this Vertex to explored
		this.scc.add(v_i);				//Add this Vertex to the SCC object
		ArrayList<Vertex> neighbors = new ArrayList<>();	//initialize the ArrayList of neighboring vertices.

		/* If reverseGraph == true, then instead of literally flipping arrows and constructing a new graph,
		 * just get the parent neighboring vertices. */
		if(reverseGraph) {
			neighbors = v_i.getParentVertices();
			if(debugOn) System.out.printf("ReverseGraph neighbors for vertex %s: %s\n", v_i, neighbors);
		}
		/* Else, if reverseGraph == false, then just get the child neighboring vertices as usual. */
		else {
			neighbors = v_i.getChildVertices();
			if(debugOn) System.out.println("Orig. graph neighbors: " + neighbors);
		}

		/* Now that we have the ArrayList of neighboring vertices, go thru each neighbor */
		for(Vertex neighbor : neighbors) {
			if(!neighbor.explored) {	//If the neighbor if unexplored, then recurse!
				if(debugOn) System.out.printf("Vertex %s's neighbor %s is unexplored! recursing...\n", v_i, neighbor);
				dfs(neighbor, reverseGraph);	//recursive call
			}
		}
		//End for

		this.t++;	//Once the for loop is over, increment the global variable t (finishing time)
		v_i.finishingTime = this.t;	//assign t to this Vertex's data field. This will be necessary in Kosaraju() method later.
		if(debugOn) System.out.printf("f(%s): %s\n", v_i.lbl, v_i.finishingTime);
	}
	//end private void dfs

	/**
	 * Class: Vertex
	 *        Vertex object.
	 */
	private class Vertex {
		int lbl, lblBackup;	//name (label no.) of vertex. Could be positive or negative.
		int finishingTime;	//finishing time. See Kosaraju() method for more details.
		ArrayList<Edge> outgoingArrows, incomingArrows;	//list of edges connected to this vertex
		boolean explored;	//whether this Vertex has been explored by DFS or not.

		/**
		 * 1-arg constructor.
		 * @param lbl the name (label) to assign to this vertex
		 */
		Vertex(int lbl) {
			this.finishingTime = -1;	//initialize time to -1
			this.explored = false;
			this.lbl = lbl;
			this.lblBackup = this.lbl;	//keep a backup of the label
			this.outgoingArrows = new ArrayList<Edge>();
			this.incomingArrows = new ArrayList<Edge>();
		}

		/**
		 * Method: getChildVertices
		 * @return an ArrayList of all neighboring child vertices
		 */
		ArrayList<Vertex> getChildVertices() {
			ArrayList<Vertex> ret = new ArrayList<>();
			for (Edge e : this.outgoingArrows) {
				ret.add(e.endingVertex);
			}
			return ret;
		}

		/**
		 * Method: getParentVertices
		 * @return an ArrayList of all neighboring parent vertices
		 */
		ArrayList<Vertex> getParentVertices() {
			ArrayList<Vertex> ret = new ArrayList<>();
			for (Edge e : this.incomingArrows) {
				ret.add(e.startingVertex);
			}
			return ret;
		}

		@Override
		/**
		 * Method: toString
		 * @return the label no. of this Vertex.
		 */
		public String toString() {
			return this.lbl + "";
		}

		/**
		 * Method: toString2
		 * @return the ArrayList of edges leaving this Vertex.
		 */
		public String toString2() {
			return this.outgoingArrows + "";
		}
	}

	/**
	 * Class: Edge
	 * Directed edge representation.
	 */
	private class Edge {
		Vertex startingVertex, endingVertex;	//the two vertices connected by this Edge.

		/**
		 * 2-arg constructor.
		 * @param v1 one end of the vertex connected to this Edge
		 * @param v2 the other end of the vertex connected to this Edge
		 */
		Edge(Vertex v1, Vertex v2) {
			this.startingVertex = v1;	//vertex from which this arrow protrudes
			this.endingVertex = v2;		//vertex which this arrow points to
		}

		@Override
		/**
		 * Method: toString
		 * @return the vertices connected by this arrow
		 */
		public String toString() {
			return this.startingVertex.lbl + "->" + this.endingVertex.lbl;
		}
	}
	//end private class Edge

	/**
	 * Class: SCC
	 *        Inner class. A SCC (Strongly Connected Component) group consists of a group of Vertices
	 *        that have equivalence relations.
	 *
	 */
	private class SCC {
		HashSet<Vertex> sccGroup;

		/**
		 * No-arg constructor.
		 */
		SCC() {
			sccGroup = new HashSet<>();
		}

		/**
		 * Method: add
		 *         Adds a vertex to this SCC.
		 * @param v the vertex to add
		 */
		void add(Vertex v) {
			sccGroup.add(v);
		}

		boolean contains(int vertexLbl) {
			Vertex v = vertexMap.get(vertexLbl);
			return sccGroup.contains(v);
		}

		@Override
		/**
		 * Method: toString
		 * @return the ArrayList of vertices to the console.
		 */
		public String toString() {
			return sccGroup + "";
		}
	}
	//end private class SCC

	public static void main(String[] args) {

		/* End user should enter "2sat*.txt" (without the quotes) as the parameter, and compare the solution output
		 * with the solution indicated in the filename for each data file. */
		for (String s : args) {
			TwoSAT_SCC twoSat = new TwoSAT_SCC(s, false);
			System.out.printf("==========================================================\nRunning %s...\n", s);
			twoSat.Kosaraju();
		}
	}
}
