import InitECandidate.Solver.WitnessRadix.HelperNonemptyPublic

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The empty helper needs only its actual ABI/header cells and mapped root;
no positive-size backing-layout assumptions are introduced. -/
theorem helper_empty_public {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word layout.table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (header : BuildEntry.Header source layout.table layout.keys layout.vals layout.primary layout.backup)
    (rootMapped : source.memaddrs (cell layout .header 24)) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source BuildProgram.body = (some (.returned (.val (.word 0#64))), target) ∧
      target.memaddrs (cell layout .header 24) ∧ target.memory (cell layout .header 24) = .word 0#64 ∧
      QueryMemory.Represents target layout.table layout.keys layout.vals 0#64 (initialTree keyFor sliceFor []) ∧
      control target = control source ∧ target.clock = source.clock ∧
      (∀ query,PublicWord layout query→target.memory query=source.memory query) := by
  obtain ⟨target, run, frame⟩ := BuildEntry.empty_builder source layout.table layout.keys layout.vals layout.primary layout.backup
    tableLocal countLocal header rootMapped
  have domainEq : target.memaddrs = source.memaddrs := congrArg (fun state => state.memaddrs) frame
  have memoryEq : target.memory = StoreWord.put source.memory (cell layout .header 24) 0#64 :=
    congrArg (fun state => state.memory) frame
  refine ⟨target, run, ?_, ?_, ?_, ?_, congrArg (fun state => state.clock) frame,?pub⟩
  case pub =>
    intro query outside
    rw [memoryEq]
    exact if_neg (outside .header 24 rfl)
  · rw [domainEq]; exact rootMapped
  · rw [memoryEq]; simp [StoreWord.put]
  · change (0#64 : BitVec 64) = 0#64
    rfl
  · exact (control_of_frame target _ frame).trans rfl

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.helper_empty_public
