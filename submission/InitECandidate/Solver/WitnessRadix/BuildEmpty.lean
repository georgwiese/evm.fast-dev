import InitECandidate.Solver.WitnessRadix.BuildInitialState
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem zero_return {F : Type} (source : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState source returnZero =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  classical
  simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem core_empty {F : Type} (source : PanSemStateFiniteExact 64 F) (destination : BitVec 64)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word destination)))
    (mapped : source.memaddrs destination) :
    evaluateHOLFiniteState source core =
      (some (.returned (.val (.word 0#64))),
        emptyLocalsHOLFinite { source with memory := StoreWord.put source.memory destination 0#64 }) := by
  classical
  have destRead : eval source (localVar "dest") = some (.val (.word destination)) := by
    simp [eval, localVar, evalHOLExact, toExact, destLocal]
  have zeroRead : eval source (.const 0#64) = some (.val (.word 0#64)) := by rfl
  have write := StoreWord.execute source (localVar "dest") (.const 0#64) destination 0#64 destRead zeroRead mapped
  let written := { source with memory := StoreWord.put source.memory destination 0#64 }
  have storeReturn : evaluateHOLFiniteState source
      (.seq (.store (localVar "dest") (.const 0#64)) returnZero) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite written) := by
    rw [evaluateHOLFiniteState_seq, write]
    simpa [fixClockHOLFinite, written] using zero_return written
  have chosen : evaluateHOLFiniteState source
      (.ite (.cmp .equal (localVar "n") (.const 0#64))
        (.seq (.store (localVar "dest") (.const 0#64)) returnZero) .skip) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite written) := by
    rw [evaluateHOLFiniteState_ite]
    simpa [localVar, evalHOLExact, toExact, countLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using storeReturn
  rw [core_shape, evaluateHOLFiniteState_seq, chosen]
  simp [fixClockHOLFinite, written, emptyLocalsHOLFinite]

/-- Complete actual helper execution for an empty witness map, from real
header/ABI cells. It writes only the empty root and uses no source clock. -/
theorem empty_builder {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals src dst : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (cells : Header source table keys vals src dst)
    (rootMapped : source.memaddrs (table + 24#64)) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source BuildProgram.body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        { source with memory := StoreWord.put source.memory (table + 24#64) 0#64 } := by
  classical
  let initial := entered source table 0#64 keys vals src dst
  have nLocal : initial.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    rw [entered_count]
    exact countLocal
  have destLocal : initial.locals.lookup (ofString "dest") = some (.val (.word (table + 24#64))) :=
    entered_binding source table 0#64 keys vals src dst ("dest", table + 24#64) (by simp [initialValues])
  have coreRun := core_empty initial (table + 24#64) nLocal destLocal rootMapped
  obtain ⟨restoreStack, frame, prefixRun⟩ := prefix_execute source table 0#64 keys vals src dst tableLocal countLocal cells
  change evaluateHOLFiniteState initial core = _ at coreRun
  rw [coreRun] at prefixRun
  refine ⟨_, prefixRun, ?_⟩
  rw [frame]
  rfl

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.empty_builder
