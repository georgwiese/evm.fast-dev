import InitECandidate.Solver.GasBudget.JournalInitProgram

namespace InitECandidate.Solver.Mpt.StateInit

/-- Keep the large constant sum algebraic: reducing additions on an
unknown natural cursor by reflexivity can exceed the kernel depth limit. -/
theorem block_end_arithmetic (start next : Nat) (number : next=start+80) :
    next+70840+64+GasBudget.Journal.Initialization.bytes=start+16848200 := by
  have bytes : GasBudget.Journal.Initialization.bytes=16777216:=by decide
  omega

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.block_end_arithmetic
