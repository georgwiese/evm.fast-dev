import InitECandidate.Solver.Input.ScalarNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- A successful original scalar memory load returns a word. This derives
the argument type from the actual read, without a speculative mapped cell. -/
theorem load_one_word {F : Type} (source : PanSemStateFiniteExact 64 F) (address : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source (.load .one address)=some value) : ∃ word,value=.val (.word word) := by
  classical
  simp only [eval] at read
  rw [evalHOLExact] at read
  simp only [isWfShapeExactHOL,↓reduceIte] at read
  generalize pointerRead : @evalHOLExact 64 F _ source.toExact (fun query=>Classical.propDecidable (source.memaddrs query)) address=pointer at read
  cases pointer with
  | none => cases read
  | some pointer =>
    cases pointer with
    | rStruct fields => cases read
    | nStruct name fields => cases read
    | val payload =>
      cases payload with
      | word pointer =>
        by_cases mapped : source.memaddrs pointer
        · cases cell : source.memory pointer with
          | word word =>
            exact ⟨word,by simpa [memLoadHOLExact,toExact,mapped,cell] using read.symm⟩
        · simp [memLoadHOLExact,toExact,mapped] at read

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.load_one_word
