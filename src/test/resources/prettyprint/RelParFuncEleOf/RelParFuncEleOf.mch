MACHINE RelParFuncEleOf
DEFINITIONS
RelParFuncEleOf(p__S, p__T) == LET S,T BE S=p__S & T=p__T IN {f|f:POW(S*T) & card(UNION(x).(x:f|{@prj1((@prj1(x), @prj2(x)))}))=card(f)} END
CONSTANTS k
PROPERTIES k:POW(INTEGER*BOOL) & k:RelParFuncEleOf(INTEGER, BOOL)
END
