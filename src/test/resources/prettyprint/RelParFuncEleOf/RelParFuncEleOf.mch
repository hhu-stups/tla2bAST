MACHINE RelParFuncEleOf
DEFINITIONS
RelParFuncEleOf(S, T) == {f|f:POW(S*T) & card(UNION(x).(x:f|{@prj1((@prj1(x), @prj2(x)))}))=card(f)}
CONSTANTS k
PROPERTIES k:POW(INTEGER*BOOL) & k:RelParFuncEleOf(INTEGER, BOOL)
END
