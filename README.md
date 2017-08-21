# Two_SAT_Satisfiability_Solver_Using_SCC

This class solves the 2SAT problem via reduction to the Strongly Connected Components (SCC) algorithm.
 
The test data file format is as follows. In each instance, the number of variables and the number of clauses is the same, and this number is specified on the first line of the file. Each subsequent line specifies a clause via its two literals, with a number denoting the variable and a "-" sign denoting logical "not". For example, if the second line of a data file is "-16808 75250", it indicates the boolean logical clause ¬x16808 v x75250.

This class will determine, for each data file, whether or not it is logically satisfiable. Since this problem reduces to the algorithm for finding the Strongly Connected Components (SCC) of a graph, this class uses that algorithm, resulting in asymtotically linear-time solution.

To run, execute TwoSAT_SCC.java along with the following parameter: 2sat*.txt. This will go thru all the test data files and output whether each one is satisfiable or not.
