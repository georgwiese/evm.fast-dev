import InitECandidate.Solver.WitnessRadix.MemeqMemory

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

/-- Actual DecCall of fixed memeq, with caller locals restored before the
continuation. The caller pays one clock plus at most four comparison clocks.
The argument/lookup premises concern real evaluated arguments and code data. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (a b : BitVec 64) (left right : ByteKeys.Key)
    (argumentValues : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word a), .val (.word b), .val (.word 32#64)])
    (code : lookupCodeHOLFinite source.code.lookup (ofString "memeq")
      [.val (.word a), .val (.word b), .val (.word 32#64)] = some (body, callee, .one))
    (argA : callee.lookup (ofString "a") = some (.val (.word a)))
    (argB : callee.lookup (ofString "b") = some (.val (.word b)))
    (length : callee.lookup (ofString "n") = some (.val (.word 32#64)))
    (leftView : MemoryBytes.ByteView source a left) (rightView : MemoryBytes.ByteView source b right)
    (leftFits : a.toNat + 32 < 2 ^ 64) (rightFits : b.toNat + 32 < 2 ^ 64)
    (little : source.be = false) (enough : 5 ≤ source.clock) :
    ∃ paid, paid ≤ 4 ∧
      evaluateHOLFiniteState source (.decCall (ofString "equal") .one (ofString "memeq") arguments continuation) =
        (let result := evaluateHOLFiniteState
          (bind { source with clock := source.clock - (paid + 1) } "equal"
            (if left = right then 1#64 else 0#64)) continuation;
         (result.1, restore source "equal" result.2)) := by
  classical
  let entry := callEntryStateHOLFinite source callee
  have entryLeft := MemoryBytes.byteView_of_fields source entry rfl rfl rfl a left leftView
  have entryRight := MemoryBytes.byteView_of_fields source entry rfl rfl rfl b right rightView
  obtain ⟨paid, bound, comparison⟩ := memory_execute entry a b left right argA argB length
    entryLeft entryRight leftFits rightFits little (by dsimp [entry, callEntryStateHOLFinite]; omega)
  have clockEq : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  have noIncrease : ¬ source.clock - 1 < source.clock - (paid + 1) := by omega
  have positive : source.clock ≠ 0 := by omega
  refine ⟨paid, bound, ?_⟩
  rw [evaluateHOLFiniteState_decCall_total]
  simp only [argumentValues, code, if_neg positive]
  rw [comparison]
  simp only [shapeOfHOLExact, shapeEqHOL, Bool.and_self, ↓reduceIte]
  simp only [fixClockHOLFinite, entry, callEntryStateHOLFinite, QueryBranch.restore,
    emptyLocalsHOLFinite, clockEq, noIncrease, ↓reduceIte, QueryBranch.bind, setVarHOLFinite]

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.call_execute
