# Two_SAT_Satisfiability_Solver_Using_SCC

This class solves the 2SAT problem via reduction to the Strongly Connected Components (SCC) algorithm.
 
The test data file format is as follows. In each instance, the number of variables and the number of clauses is the same, and this number is specified on the first line of the file. Each subsequent line specifies a clause via its two literals, with a number denoting the variable no. and a "-" sign denoting logical "not". For example, if the second line of a data file is "-16808 75250", it indicates the boolean logical clause ¬x16808 OR x75250. Furthermore, the clauses in each line are connected by the logical AND operator.

Given the above for each data file, this class will determine whether or not the data file represents a logically satisfiable series of logical statements. Since this problem reduces to the algorithm for finding the Strongly Connected Components (SCC) of a graph, this class uses that algorithm, resulting in asymtotically linear-time solution.

To run, execute TwoSAT_SCC.java along with the following parameter: 2sat*.txt. This will go thru all the provided test data files one by one and output whether each is satisfiable or not. The user can check the output solution against the solution specified in the file name for each data file.
