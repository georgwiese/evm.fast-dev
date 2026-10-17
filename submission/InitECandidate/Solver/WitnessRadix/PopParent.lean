import InitECandidate.Solver.WitnessRadix.PopReads
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.WitnessRadix.PopProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem after_parent_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (parent bit oldBit oldDest : BitVec 64)
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word oldBit)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word oldDest)))
    (mapped : source.memaddrs parent) (stored : source.memory parent = .word bit) :
    evaluateHOLFiniteState source afterParent =
      (some .continue, bind (bind source "bit" (bit + 1#64)) "dest" (parent + 16#64)) := by
  classical
  have bitRun := StateSteps.assign_execute source "bit" bitExpression oldBit (bit + 1#64)
    bitLocal (parent_bit_read source parent bit parentLocal mapped stored)
  let bitState := bind source "bit" (bit + 1#64)
  have notParent : ofString "bit" ≠ ofString "parent" := by decide
  have notDest : ofString "bit" ≠ ofString "dest" := by decide
  have parent' : bitState.locals.lookup (ofString "parent") = some (.val (.word parent)) := by
    simp [bitState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notParent, parentLocal]
  have dest' : bitState.locals.lookup (ofString "dest") = some (.val (.word oldDest)) := by
    simp [bitState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notDest, destLocal]
  have destRun := StateSteps.assign_execute bitState "dest" destExpression oldDest (parent + 16#64)
    dest' (parent_dest_read bitState parent parent')
  rw [afterParent]
  rw [StateSteps.next_sequence source bitState bitAssignment _ bitRun (Nat.le_refl _)]
  rw [StateSteps.next_sequence bitState (bind bitState "dest" (parent + 16#64)) destAssignment _ destRun (Nat.le_refl _)]
  rw [evaluateHOLFiniteState_continue]

/-- Loading the pending parent and finishing the pop restores the scoped
parent binding and changes only bit/dest. -/
theorem parent_declaration {F : Type} (source : PanSemStateFiniteExact 64 F)
    (parent bit oldBit oldDest : BitVec 64)
    (readParent : eval source (pendingExpression "pending_node") = some (.val (.word parent)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word oldBit)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word oldDest)))
    (mapped : source.memaddrs parent) (stored : source.memory parent = .word bit) :
    evaluateHOLFiniteState source
      (.dec (ofString "parent") .one (pendingExpression "pending_node") afterParent) =
      (some .continue, bind (bind source "bit" (bit + 1#64)) "dest" (parent + 16#64)) := by
  classical
  let parentState := bind source "parent" parent
  have notBit : ofString "parent" ≠ ofString "bit" := by decide
  have notDest : ofString "parent" ≠ ofString "dest" := by decide
  have parent' : parentState.locals.lookup (ofString "parent") = some (.val (.word parent)) := by
    simp [parentState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have bit' : parentState.locals.lookup (ofString "bit") = some (.val (.word oldBit)) := by
    simp [parentState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notBit, bitLocal]
  have dest' : parentState.locals.lookup (ofString "dest") = some (.val (.word oldDest)) := by
    simp [parentState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notDest, destLocal]
  have afterRun := after_parent_execute parentState parent bit oldBit oldDest parent' bit' dest' mapped stored
  simp only [eval] at readParent
  rw [evaluateHOLFiniteState_dec_total]
  simp only [readParent, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState parentState afterParent;
    (output.1, restore source "parent" output.2)) = _
  rw [afterRun]
  change (some (PanSemResultExact.continue : PanSemResultExact 64), restore source "parent"
    (bind (bind parentState "bit" (bit + 1#64)) "dest" (parent + 16#64))) = _
  rw [restore_bind_other source _ "parent" "dest" _ notDest,
    restore_bind_other source parentState "parent" "bit" _ notBit]
  have restored : restore source "parent" parentState = source := restore_bound _ _ _
  rw [restored]

end InitECandidate.Solver.WitnessRadix.PopProgram

#print axioms InitECandidate.Solver.WitnessRadix.PopProgram.parent_declaration
