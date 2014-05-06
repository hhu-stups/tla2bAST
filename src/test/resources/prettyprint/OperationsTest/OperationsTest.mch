MACHINE OperationsTest
VARIABLES a, b, c
INVARIANT
(a : INTEGER & b : INTEGER) & c : INTEGER
INITIALISATION
a, b, c:((a = 1 & b = 2) & c = 3)
OPERATIONS
 begin1 = BEGIN a,b,c := 1,2,3 END;

 any1 = ANY a_n, b_n, c_n WHERE (((a_n : INTEGER & b_n : INTEGER) & c_n : INTEGER) & a_n + 1 = 2) & (b_n = b & c_n = c) THEN a,b,c := a_n,b_n,c_n END;

 any2 = ANY a_n, b_n, c_n WHERE ((((1 = 1 & a_n : INTEGER) & b_n : INTEGER) & c_n : INTEGER) & a_n + 1 = 2) & (b_n = b & c_n = c) THEN a,b,c := a_n,b_n,c_n END;

 any3 = ANY a_n, b_n, c_n WHERE ((((a_n : INTEGER & b_n : INTEGER) & c_n : INTEGER) & a_n = 2) & a_n > 1) & (b_n = b & c_n = c) THEN a,b,c := a_n,b_n,c_n END;

 any4 = ANY a_n, b_n, c_n WHERE ((a_n : INTEGER & b_n : INTEGER) & c_n : INTEGER) & ((a_n = a & b_n = b) & c_n = c) THEN a,b,c := a_n,b_n,c_n END;

 select = SELECT 1 = 1 THEN a,b,c := 1,2,3 END
END