open ctl[State]

abstract  sig Bit {}
one sig _0, _1 extends Bit{}

abstract  sig state {}
one sig _busy, _ready extends state{}


sig State {
 transition: some State,
 request : one Bit,
 state : one state // _0 busy _1 ready
}

fact modelDefinition {
 // constraints on states (State)
 all s:State | stateConstraints[s]
 // init state constraints
 // the function initialState is defined in the CTL module
 all s:State | s in initialState iff init[s]
 // only defined transitions are valid
 // the function nextState is defined in the CTL module
 all s,s':State| s->s' in nextState iff
   validTransition[s,s']
 // ensure that two states with the same features are equivalent
 all s,s':State| stateEquality[s,s']
}

pred init [s:State]{
 s.request = _1
}

pred stateConstraints [s: State] {
    
}

pred validTransition[s,s' : State ]{
    (s.request = _1) => (s'.state = _busy) and (s'.state = _busy or s'.state = _ready)
}

pred stateEquality[s,s' : State]{
(  s.request = s'.request and s.state = s'.state => s = s' )
}

fact modelWellMappedToCTLModule{
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

run showExamples { } for exactly 4 State

assert letsModelCheckThisFormula{
    ctl_mc[ ag[{s:State | completeThis[s]}] ]
}
pred completeThis [s:State]{
}
check letsModelCheckThisFormula for 3 // should find no counterexample
check letsModelCheckThisFormula for 4 // should find a counterexample
