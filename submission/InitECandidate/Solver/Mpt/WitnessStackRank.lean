import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram

namespace InitECandidate.Solver.Mpt.WitnessStackRank

/-- Arithmetic model for original238's control stack. Its connection to
actual record memory and helper cursor preservation is a separate obligation. -/
inductive Phase where | returning | decode | resolve
  deriving DecidableEq

inductive Frame where | extension | branch (index : Fin 16)
  deriving DecidableEq

def phaseWeight : Phase→Nat | .returning=>0 | .decode=>1 | .resolve=>2
def frameWeight : Frame→Nat | .extension=>1 | .branch index=>3*(15-index.val)+1
def pending (stack : List Frame) : Nat := (stack.map frameWeight).sum
def rank (remaining : Nat) (stack : List Frame) (phase : Phase) (go : Bool) : Nat :=
  48*remaining+pending stack+phaseWeight phase+(if go then 1 else 0)
def recordsLeft (cursor floor : Nat) : Nat := (cursor-floor)/88

theorem resolve_decode (remaining : Nat) (stack : List Frame) : rank remaining stack .decode true<rank remaining stack .resolve true := by
  simp only [rank,phaseWeight]
  omega

theorem terminal (remaining : Nat) (stack : List Frame) : rank remaining stack .returning true<rank remaining stack .decode true := by
  simp only [rank,phaseWeight]
  omega

theorem push (remaining : Nat) (positive : 0<remaining) (stack : List Frame) (frame : Frame) :
    rank (remaining-1) (frame::stack) .resolve true<rank remaining stack .decode true := by
  have weight : frameWeight frame≤46 := by cases frame with
    | extension => decide
    | branch index => have bound:=index.isLt; simp only [frameWeight]; omega
  simp only [rank,pending,List.map_cons,List.sum_cons,phaseWeight]
  omega

theorem branch_next (remaining : Nat) (stack : List Frame) (index : Nat) (nextInside : index+1<16) :
    rank remaining (.branch ⟨index+1,nextInside⟩::stack) .resolve true<
      rank remaining (.branch ⟨index,by omega⟩::stack) .returning true := by
  simp only [rank,pending,List.map_cons,List.sum_cons,frameWeight,phaseWeight]
  omega

theorem pop (remaining : Nat) (stack : List Frame) (frame : Frame) :
    rank remaining stack .returning true<rank remaining (frame::stack) .returning true := by
  have positive : 0<frameWeight frame := by cases frame <;> simp [frameWeight]
  simp only [rank,pending,List.map_cons,List.sum_cons,phaseWeight]
  omega

theorem finish (remaining : Nat) : rank remaining [] .returning false<rank remaining [] .returning true := by
  simp [rank,pending,phaseWeight]

theorem allocated88 (cursor floor next : Nat) (below : floor≤next) (decrease : next+88=cursor) : recordsLeft cursor floor=recordsLeft next floor+1 := by
  unfold recordsLeft
  omega

theorem initial_records : recordsLeft 2713714688 2701135872=142941 := by decide
theorem initial_rank : rank (recordsLeft 2713714688 2701135872) [] .decode true=6861170 := by decide

end InitECandidate.Solver.Mpt.WitnessStackRank

#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.resolve_decode
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.terminal
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.push
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.branch_next
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.pop
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.finish
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.allocated88
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.initial_records
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.initial_rank
