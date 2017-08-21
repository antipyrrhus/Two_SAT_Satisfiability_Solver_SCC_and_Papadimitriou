import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.Iterator;
import java.util.StringTokenizer;

/** Class: TwoSAT_Papadimitriou.java
 *  @author Yury Park
 *
 *  This class - 2-SAT problem solver using Papadimitriou's random walk algorithm which finds the correct solution
 *  with a high probability. Uses the same test data files as TwoSAT_SCC.java.
 *
 */
public class TwoSAT_Papadimitriou {

	private String fileName;			//name of txt file to read data from in order to construct a graph
	private Set<Integer> setOfInts;		//All integer values that appear in the txt file.
	private Variable[] varArr;			//Maps Variable to its integer label value.
	private ArrayList<Clause> clauseAL;	//All boolean clauses that appear in the txt file.
	private Clause[] clauseArr;			//Array of all boolean clauses that appear in the txt file (To help with efficiency)
	private Map<Integer, HashSet<Clause>> clauseMap;	//Maps integer value to all clauses that contain that integer (regardless of - or + sign)
	private int numOfVars;				//total number of variables
	private int numOfClauses;			//total number of clauses
	private ArrayList<Clause> falseClausesAL;	//Keeps track of false Clauses (used by papadimitriou() method)

	private static boolean debugOn;

	/**
	 * 2-arg constructor.
	 * @param fileName
	 * @param debugMode
	 */
	public TwoSAT_Papadimitriou(String fileName, boolean debugMode) {
		this.fileName = fileName;
		this.setOfInts = new HashSet<Integer>();
		this.clauseAL = new ArrayList<Clause>();
		this.clauseMap = new HashMap<Integer, HashSet<Clause>>();
		this.falseClausesAL = new ArrayList<Clause>();
		debugOn = debugMode;

		build();
	}

	/**
	 * Method: build
	 * Reads data from txt file, constructs Variables and Clauses, then prunes unnecessary clauses.
	 */
	private void build() {

		try {
			BufferedReader rd = new BufferedReader(new FileReader(new File(fileName)));

            //Read the first line, which contains info re: total no. of variables and total no. clauses
            String line = rd.readLine();

            StringTokenizer tokenizer = new StringTokenizer(line);
            this.numOfVars = Integer.parseInt(tokenizer.nextToken());	//1st entry in the first line contains total no. of variables

            /* Depending on the txt file, there may or may not be a 2nd entry in the first line. If there is,
             * then it contains the total no. of clauses. If there isn't, then total no. of vars = total no. of clauses. */
            if (tokenizer.hasMoreTokens()) this.numOfClauses = Integer.parseInt(tokenizer.nextToken());
            else this.numOfClauses = this.numOfVars;

            System.out.printf("No. of clauses BEFORE pruning: %s\nNo. of variables BEFORE pruning: %s\n", this.numOfClauses, this.numOfVars);

            this.varArr = new Variable[numOfVars + 2];	//Assumes that Variables will be indexed from 1 to numOfVars.
//            System.out.println(this.varArr.length);
            this.clauseArr = new Clause[numOfClauses];	//Assumes that Clauses will be indexed from 0 to numOfClauses - 1.

            int index = 0;
            while (index < this.numOfClauses) {	//read clause from each subsequent line
            	line = rd.readLine();
                tokenizer = new StringTokenizer(line);

                /* Read the two int values from this line.
                 * These int values could be positive or negative.  For example, the following line:
                 *
                 * -10492 51342
                 *
                 * indicates that the variable NAMES are 10492 and 51341, and the minus sign indicates the boolean value NOT.
                 * The space between the two integers indicates the boolean value OR.
                 * So it means: NOT 10492 OR 51342.
                 *
                 * To make this easier to understand, imagine the following clause:
                 * -A B
                 * This would mean NOT A OR B. */
                int intValue1 = Integer.parseInt(tokenizer.nextToken());
                setOfInts.add(intValue1);	//Remember this int value by adding to set. Auto-takes care of any duplicates
                Variable var1 = this.getOrCreateVariable(intValue1);	//custom method

                int intValue2 = Integer.parseInt(tokenizer.nextToken());
                setOfInts.add(intValue2);	//Remember this int value by adding to set. Auto-takes care of any duplicates
                Variable var2 = this.getOrCreateVariable(intValue2);

                Clause c = new Clause(index, var1, intValue1, var2, intValue2);	//Construct new Clause (inner nested class)
                clauseArr[index++] = c;	//Add Clause to Array

                /* For efficiency, we'll update this map which maps each Variable's label no.
                 * (which equals the absolute value of intValue1 and of intValue2) to a HashSet (list) of
                 * Clauses that contain that label no. Doing this now makes it easier later to prune
                 * all Clauses that contain a specific Variable. */
                HashSet<Clause> clauseHS1 = clauseMap.get(var1.label);
                HashSet<Clause> clauseHS2 = clauseMap.get(var2.label);
                if (clauseHS1 == null) clauseHS1 = new HashSet<Clause>();
                if (clauseHS2 == null) clauseHS2 = new HashSet<Clause>();
                clauseHS1.add(c);
                clauseHS2.add(c);
                clauseMap.put(var1.label, clauseHS1);
                clauseMap.put(var2.label, clauseHS2);
            }
            //end while

            rd.close();
            if (debugOn) {
            	System.out.println("All clauses BEFORE pruning:");
            	for (Clause c : this.clauseArr) {
            		if (c != null) System.out.println(c);
            	}

            	for (Clause c : this.clauseArr) {
            		if (c != null) System.out.println(c.toString2());
            	}
            }
            //end if (debugOn)


            /* Now we prune unnecessary clauses. What does this mean? 
             * Well, consider the following toy data set of clauses:
             * 
             * -1  4
             * -1  2
             *  2 -4
             *  3  1
             *
             *  This translates to:
             *  NOT 1 OR     4
             *  NOT 1 OR     2
             *      2 OR NOT 4
             *      3 OR     1
             *
             *  Now note that both -1 and 1 appear in the above clauses. We shouldn't prune these.
             *
             *  But note that only 2 (and not -2) appears. So this means that we can (implicitly) assign value TRUE
             *  to 2, and simply prune ALL clauses containing 2 (because those clauses are now ALL true anyway).
             *
             *  Same for 3 (since -3 doesn't appear anywhere): so we again (implicitly) assign TRUE to 3 and
             *  prune ALL clauses containing 3.
             *
             *  After pruning all clauses containing 1 or 3, we get:
             *  -1  4
             *
             *  Great, we're down to just one statement. and NOW look! Previously we couldn't prune 1, -1, 4, and -4.
             *  But after pruning, we see that 1 and -4 are gone! So we only see -1 and 4. Meaning we can prune
             *  all clauses containing -1 and 4 as well! (while implicitly assigning FALSE to 1 so that -1 = TRUE, and
             *  assigning TRUE to 4)...
             *
             *  After the 2nd pruning, we get an EMPTY set of clauses.
             *
             *  So the point is, to keep pruning and reducing the set of clauses until we can't do so anymore.
             *  */
            System.out.println("Pruning unnecessary clauses...");
            boolean keepGoing = true;	//sentinel value

            //outer loop
            while (keepGoing) {
            	keepGoing = false;

            	/* Go thru each integer and see if both its positive and negative counterparts exist.
            	 * If both exist, continue...if not, we delete ALL clauses containing the Variable with
            	 * the corresponding label no (which equals the abs. value of the integer) */
            	Iterator<Integer> iter = setOfInts.iterator();

            	//inner loop
            	while (iter.hasNext()) {
	            	int nextInt = iter.next();
	            	if (setOfInts.contains(-nextInt)) continue;

	            	/* Go ahead and delete ALL clauses containing this variable!
	            	 * And also set the sentinel value to true, because we might need to RE-prune afterwards
	            	 * by repeating the outer loop */
	            	keepGoing = true;
	            	/* Go thru every Clause in the HashSet<Clause> which is gotten by invoking
	            	 * this.clauseMap.get(Math.abs(nextInt)), and delete every such Clause from the Array.
	            	 * (Note that using Array is faster than ArrayList, notwithstanding some wasted memory space. */
	            	for (Clause c : this.clauseMap.get(Math.abs(nextInt))) {
	            		this.clauseArr[c.lbl] = null;
	            	}
            	}
            	//end while (iter.hasNext())

//            	System.out.println("rebuilding clauseMap and setOfInts...");

            	/* Now that we pruned some Clauses from the Array, we'll need to update
            	 * the clauseMap and setOfInts prior to the next outer loop iteration */
            	setOfInts.clear();	//reset before new update
            	clauseMap.clear();	//reset before new update

            	/* Go thru every remaining clause */
            	for (Clause c : this.clauseArr) {
            		if (c == null) continue;	//If this clause has been deleted (or was never created), continue

            		/* Every clause consists of two Variable labels (positive integers) and two corresponding signs
            		 * (negative or positive). So depending on the sign, save positive or negative integer to the set. */
            		setOfInts.add(c.sign1 == true ? c.var1.label : -c.var1.label);
            		setOfInts.add(c.sign2 == true ? c.var2.label : -c.var2.label);

            		/* For efficiency, we'll update this map which maps each Variable's label no.
                     * to a HashSet (list) of Clauses that contain that label no.
                     * Doing this now makes it easier later to prune
                     * all Clauses that contain a specific Variable. */
            		HashSet<Clause> clauseHS1 = clauseMap.get(c.var1.label);
                    HashSet<Clause> clauseHS2 = clauseMap.get(c.var2.label);
                    if (clauseHS1 == null) clauseHS1 = new HashSet<Clause>();
                    if (clauseHS2 == null) clauseHS2 = new HashSet<Clause>();
                    clauseHS1.add(c);
                    clauseHS2.add(c);
                    clauseMap.put(c.var1.label, clauseHS1);
                    clauseMap.put(c.var2.label, clauseHS2);
            	}
            	//end for (Clause c : this.clauseArr)
            }
            //end while (keepGoing)

            /* All pruning done. Now we'll add surviving Clauses to an ArrayList, and also update
             * the total number of Clauses and total number of surviving Variables. */
            Arrays.fill(this.varArr, null);	//reset and prepare to re-update the Array of surviving Variables
            this.numOfVars = 0;
            this.numOfClauses = 0;

            for (Clause c : this.clauseArr) {
            	if (c == null) continue;
            	clauseAL.add(c);	//Add every surviving Clause to ArrayList

            	if (this.varArr[c.var1.label] == null) {
            		this.numOfVars++;
            		this.varArr[c.var1.label] = c.var1;	//Add every surviving Variable to varArray
            	}
            	if (this.varArr[c.var2.label] == null) {
            		this.numOfVars++;
            		this.varArr[c.var2.label] = c.var2;	//Add every surviving Variable to varArray
            	}
            }

            this.numOfClauses = clauseAL.size();

            System.out.println("No. of clauses AFTER pruning: " + numOfClauses);
            System.out.println("No. of variables AFTER pruning: " + numOfVars);


            if (debugOn) {
            	System.out.println("All clauses AFTER pruning:");
            	for (Clause c : this.clauseAL) {
            		System.out.println(c);
            	}
            	for (Clause c : this.clauseAL) {
            		System.out.println(c.toString2());
            	}
            }
            //end if (debugOn)

  		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		//end try/catch
	}
	//end private void build

	/**
	 * Method: getOrCreateVariable
	 * @param intValue given integer value. Could have a minus sign or not.
	 * @return a Variable matching the given value (without the minus sign if any), or
	 *         constructs a new Variable matching the same and returns it.
	 */
	private Variable getOrCreateVariable(int intValue) {
		if (this.varArr[Math.abs(intValue)] == null) {	//See if a Variable with the given positive label already exists
			//If not, create variable with random boolean assignment
			Variable var = new Variable(Math.abs(intValue), new Random().nextInt(2) == 0 ? false : true);
        	this.varArr[Math.abs(intValue)] = var;
        	return var;
		}
		else {
			return this.varArr[Math.abs(intValue)];
		}
	}

	/**
	 * Method: papadimitriou. The random walk algorithm for solving 2-SAT.
	 * @return true if the clauses are satisfiable, false otherwise.
	 */
	public boolean papadimitriou() {
		if (this.clauseAL.isEmpty()) return true;	//If there are no clauses, auto-return true
		int n = this.numOfVars;

		//outer loop
		for (int i = 1; i <= n; i *= 2) {
			//check if current assignment satisfies all clauses
			boolean allClausesAreTrue = this.allClausesAreTrue();	//custom method
			System.out.printf("running iteration i = %s...\n", i);

			//inner
			for (int j = 1; j <= 2 * Math.pow(n, 2); j++) {
				//check if current assignment satisfies all clauses; if so, halt and report this fact
				if (allClausesAreTrue) return true;	//If all clauses are true, then we're done. Stop immediately.

				//Otherwise, pick random unsatisfied (false) clause and randomly flip one of the variables' boolean value
				Clause falseClause = falseClausesAL.get(new Random().nextInt(falseClausesAL.size()));	//pick false clause at random
				Variable randomVarInFalseClause = new Random().nextInt(2) == 0 ? falseClause.var1 : falseClause.var2;
				randomVarInFalseClause.value = !randomVarInFalseClause.value;	//flip the boolean value for the random Var

				/* Now that we flipped one Variable, re-compute every clause */
				allClausesAreTrue = this.allClausesAreTrue();
			}
			//end for j

			//Inner loop is over. We haven't yet found a satisfiable assignment for each variable.
			//Choose another random initial assignment from scratch and get ready for the next outer loop
			for (Clause c : this.clauseAL) {
				c.var1.value = new Random().nextInt(2) == 0 ? false : true;
				c.var2.value = new Random().nextInt(2) == 0 ? false : true;
			}
		}
		//end for i

		/* If the above outer loop ends without returning true, we assume that the clauses are probably unsatisfiable. */
		return false;
	}

	/**
	 * Method: allClausesAreTrue
	 * @return true if all clauses are satisfiable with the current variable assignments. Return false otherwise.
	 *         Also keeps track of any false clauses in a global ArrayList.
	 */
	private boolean allClausesAreTrue() {

		/*Compute the Truth value of each Clause. For example, if a clause is as follows:
		 * -1205 2010
		 *
		 * where Variable 1205 has been randomly assigned TRUE and 2010 randomly assigned FALSE, then the above becomes:
		 * -TRUE v FALSE
		 *
		 * which is the same as:
		 * FALSE v FALSE
		 *
		 * AKA:
		 * FALSE. */
		boolean allClausesAreTrue = true;	//sentinel value
		this.falseClausesAL.clear();		//Reset global AL. Keeps track of any false clauses

		for (Clause c : this.clauseAL) {
			if (c.computeOverallValue() == false) {
				allClausesAreTrue = false;	//update sentinel value
				falseClausesAL.add(c);		//Add false clause to global AL
			}
		}
		return allClausesAreTrue;
	}

	/**
	 *  Class: Variable
	 *
	 *  This class - The Variable class (nested class)
	 *  Purpose - Each variable has a label (a positive integer) and an assigned boolean value (TRUE or FALSE)
	 */
	private class Variable {
		int label;
		boolean value;
		
		Variable (int label, boolean value) {
			this.label = label;
			this.value = value;
		}

		/**
		 * Method: toString
		 * @return
		 */
		@Override
		public String toString() {
			return String.format("var%s%s", label, String.valueOf(value).toUpperCase());
		}
	}
	//end private class Variable

	/**
	 *  Class: Clause
	 *
	 *  This class - The Clause class (nested class)
	 *  Purpose - Each Clause object consists of two Variables and their corresponding signs.
	 */
	private class Clause {
		int lbl;				//Every clause has a label number
		Variable var1, var2;	//Every clause consists of two variables (with an implicit OR between them)
		boolean sign1, sign2;	//Each variable is accompanied by a sign -- either positive (true) or negative (false)
		boolean overallValue;

		/**
		 * 5-arg constructor
		 * @param lbl 		The clause's label no.
		 * @param v1  		Variable 1
		 * @param sign1		The sign accompanying Variable 1 (positive (true) or negative (false))
		 * @param v2		Variable 2
		 * @param value2	The sign accompanying Variable 2 (positive (true) or negative (false))
		 */
		Clause (int lbl, Variable v1, int sign1, Variable v2, int sign2) {
			this.lbl = lbl;
			var1 = v1;
			this.sign1 = (sign1 >= 0 ? true : false);
			var2 = v2;
			this.sign2 = (sign2 >= 0 ? true : false);
		}

		/**
		 * Method: computeOverallValue
		 * @return true if this Clause is TRUE, false otherwise.
		 */
		boolean computeOverallValue() {
			/* Depending on the sign, we might need to flip the boolean value of one or both Variables. For example,
			 * the following Clause:
			 *
			 * -15 13
			 *
			 * Indicates that var1 = 15 (with a negative sign preceding it) and var2 = 13.
			 * Now let's assume that var1 is assigned a value of TRUE, and var2 FALSE. Then the clause is equivalent to:
			 *
			 * -TRUE v FALSE
			 *
			 * which resolves to FALSE v FALSE. So overallValue is FALSE. */
			boolean firstValue = (sign1 == true ? var1.value : !var1.value);
			boolean secondValue = (sign2 == true ? var2.value : !var2.value);
			this.overallValue = firstValue || secondValue;	//cache this value for more efficiency
			return overallValue;
		}

		/**
		 * Method: toString
		 * @return
		 */
		@Override
		public String toString() {
			return String.format("(%s%s v %s%s)", sign1 == true ? "" : "-", var1, sign2 == true ? "" : "-", var2);
		}

		public String toString2() {
			return String.format("(%s)", String.valueOf(overallValue).toUpperCase());
		}
	}
	//end private class Clause

	/**
	 * Method: main
	 * @param args
	 */
	public static void main(String[] args) {

		/* End user should enter "2sat*.txt" (without the quotes) as the parameter, and compare the solution output
		 * with the solution indicated in the filename for each data file. */
		long startTime = System.currentTimeMillis();
		for (String s : args) {
			System.out.printf("==========================================================\nRunning %s...\n", s);
			TwoSAT_Papadimitriou twoSat = new TwoSAT_Papadimitriou(s, false);
			System.out.printf("Satisfiable? %s\n", twoSat.papadimitriou());
		}
		System.out.printf("Total elapsed time (in millisecs): %s\n", System.currentTimeMillis() - startTime);
	}
}
