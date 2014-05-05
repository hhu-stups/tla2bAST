MACHINE OperationsTest
VARIABLES a, b, c
INVARIANT
(a : INTEGER & b : INTEGER) & c : INTEGER
INITIALISATION
a, b, c:((a = 1 & b = 2) & c = 3)
OPERATIONS
 begin1 = BEGIN skip END;

 begin2 = BEGIN a,b,c := 1,2,3 END;

 any1 = ANY a_n WHERE (a_n : INTEGER & a_n + 1 = 2) & TRUE = TRUE THEN a := a_n END;

 any2 = ANY a_n WHERE ((1 = 1 & a_n : INTEGER) & a_n + 1 = 2) & TRUE = TRUE THEN a := a_n END;

 any3 = ANY a_n WHERE ((a_n : INTEGER & a_n = 2) & a_n > 1) & TRUE = TRUE THEN a := a_n END;

 select = SELECT 1 = 1 THEN a,b,c := 1,2,3 END
END
