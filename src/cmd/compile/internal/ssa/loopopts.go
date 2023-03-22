package ssa

func loopOpts(f *Func) {
	var indVars map[*Block]indVar
	for _, v := range findIndVar(f) {
		if indVars == nil {
			indVars = make(map[*Block]indVar)
		}
		indVars[v.entry] = v
	}
}
