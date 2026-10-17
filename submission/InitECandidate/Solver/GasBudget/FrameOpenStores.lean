import InitECandidate.Solver.GasBudget.FrameOpenProgram

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual continuation-record fields, global activation and child return.
These straight-line instructions consume no Pancake evaluator clocks. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record child parent continuation kind message : BitVec 64)
    (recordLocal : source.locals.lookup (ofString "rec") = some (.val (.word record)))
    (childLocal : source.locals.lookup (ofString "child") = some (.val (.word child)))
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (mapped : ∀ offset ∈ ([0, 8, 16, 40] : List Nat), source.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source afterClear =
      (some (.returned (.val (.word child))), emptyLocalsHOLFinite {source with
        globals := (source.globals.update (ofString "ev", .val (.word child))).update
          (ofString "cur_cont", .val (.word record))
        memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes record (recordFields parent continuation kind message))}) := by
  have reads : ∀ field ∈ recordFields parent continuation kind message, field.value.Ready source "unused" 0#64 := by
    intro field member
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact parentLocal
    · exact continuationGlobal
    · exact kindLocal
    · exact messageLocal
  have fieldsMapped : ∀ field ∈ recordFields parent continuation kind message, source.memaddrs (record + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  have separate : ∀ reader ∈ recordFields parent continuation kind message, ∀ writer ∈ recordFields parent continuation kind message,
      reader.value.Avoid 0#64 (record + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer _
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  have fieldsRun := FieldStores.execute source "rec" "unused" record 0#64 (recordFields parent continuation kind message)
    recordLocal reads fieldsMapped separate activate
  let stored := {source with memory := (WitnessRadix.WordWrites.write source.memory (FieldStores.writes record (recordFields parent continuation kind message)))}
  let first := {stored with globals := stored.globals.update (ofString "ev", .val (.word child))}
  let final := {first with globals := first.globals.update (ofString "cur_cont", .val (.word record))}
  have assignChild : evaluateHOLFiniteState stored (.assign .global (ofString "ev") (localVar "child")) = (none, first) := by
    have scalarLocal : stored.locals.lookup (ofString "child") = some (.val (.word child)) := childLocal
    have scalarGlobal : stored.globals.lookup (ofString "ev") = some (.val (.word parent)) := evGlobal
    simp [evaluateHOLFiniteState_assign, localVar, evalHOLExact, toExact, scalarLocal,
      isValidValueHOLExact, lookupKvarHOLExact, scalarGlobal, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, first]
  have assignRecord : evaluateHOLFiniteState first (.assign .global (ofString "cur_cont") (localVar "rec")) = (none, final) := by
    have scalarLocal : first.locals.lookup (ofString "rec") = some (.val (.word record)) := recordLocal
    have scalarGlobal : first.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by
      simpa [first, HolFiniteMapExact.update, FUPDATE, ofString] using continuationGlobal
    simp [evaluateHOLFiniteState_assign, localVar, evalHOLExact, toExact, scalarLocal,
      isValidValueHOLExact, lookupKvarHOLExact, scalarGlobal, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, final]
  have returned : evaluateHOLFiniteState final (.return (localVar "child")) = (some (.returned (.val (.word child))), emptyLocalsHOLFinite final) := by
    have scalarLocal : final.locals.lookup (ofString "child") = some (.val (.word child)) := childLocal
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, scalarLocal, shapeOfHOLExact]
  have tailRun := WitnessRadix.StateSteps.next_sequence first final
    (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child")) assignRecord (Nat.le_refl _)
  rw [returned] at tailRun
  have activeRun := WitnessRadix.StateSteps.next_sequence stored first
    (.assign .global (ofString "ev") (localVar "child"))
    (.seq (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child"))) assignChild (Nat.le_refl _)
  rw [tailRun] at activeRun
  change evaluateHOLFiniteState stored activate = (some (.returned (.val (.word child))), emptyLocalsHOLFinite final) at activeRun
  change evaluateHOLFiniteState source afterClear = evaluateHOLFiniteState stored activate at fieldsRun
  rw [activeRun] at fieldsRun
  exact fieldsRun

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.stores_execute
