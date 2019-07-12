open ctl[State]

abstract sig Bit {}
one sig _0, _1 extends Bit{}

sig State {
  transition: some State,
  L: one Bit,
  R: one Bit
}

fact modelDefinition {
  // constraints on states (State)
  all s: State | stateConstraints[s]
  // init state constraints
  // the function initialState is defined in the CTL module
  all s: State | s in initialState iff init[s]
  // only defined transitions are valid 
  // the function nextState is defined in the CTL module
  all s,s': State | s->s' in nextState iff validTransition[s,s']
  // ensure that two states with the same features are equivalent
  all s,s': State | stateEquality[s,s']
}

pred init [s: State] {
  // TODO 
  s.L = _0 and s.R = _0
}

pred stateConstraints [s: State] { 
  // You shouldn't need to add anything here for the two-bit counter
}

pred validTransition[s, s': State] {
  // TODO
  s.L != s.R implies s'.L = _1 else s'.L = _0
  s.R = _1 implies s'.R = _0 else s'.R = _1
}

pred stateEquality[s,s' : State] {
  // TODO
  s = s' iff (s.R = s'.R and s.L = s'.L)
}

fact modelWellMappedToCTLModule {
  initialStateAxiom
  totalityAxiom
}

pred initialStateAxiom {
	some s: State | s in initialState
}

pred totalityAxiom {
  all s,s' : State |
    s->s' in nextState iff s' in s.transition
}

run showExamples { } for 5 

assert letsModelCheckThisFormula{
	ctl_mc[ ag[{s:State | completeThis[s]}] ]
}

pred completeThis [s:State] {
  // TODO
  s.R = _0 or s.L = _0
}

check letsModelCheckThisFormula for 3 // should find no counterexample

check letsModelCheckThisFormula for 4 // should find a counterexample