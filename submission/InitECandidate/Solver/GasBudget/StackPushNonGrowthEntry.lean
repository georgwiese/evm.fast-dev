import InitECandidate.Solver.GasBudget.StackPushProgram

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sp capacity : BitVec 64) :=
  bind (bind source "sp" sp) "cap" capacity

/-- Reach the genuine stack_push stores from an actual normal body when
the owned stack has a free existing slot. Both header mappings follow from
the actual reads, and the two original guards execute without a call clock. -/
theorem non_growth_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp capacity : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spCell : source.memory (frame + 16#64) = .word sp) (capCell : source.memory (frame + 232#64) = .word capacity)
    (room : sp < capacity) (bounded : capacity.toNat ≤ 1024)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ inner, source.memaddrs (frame + 16#64) ∧ source.memaddrs (frame + 232#64) ∧
      evaluateHOLFiniteState (entered source sp capacity) writes = (some (.returned value), inner) ∧
      post = restore source "sp" (restore (bind source "sp" sp) "cap" inner) := by
  rw [body_shape] at normal
  obtain ⟨spValue, spPost, spRead, spTyped, spRun, spPostEq⟩ :=
    Input.CallNormal.declaration_normal_entry source post "sp" .one (frameLoad 16#64) afterSP value normal
  have spMapped := Input.load_one_mapped source (frameAddress 16#64) (frame + 16#64) spValue (address_read source frame 16#64 ev) spRead
  have spActual := frame_read source frame 16#64 sp ev spMapped spCell
  have spEq : spValue = .val (.word sp) := Option.some.inj (spRead.symm.trans spActual)
  subst spValue
  let first := bind source "sp" sp
  rw [cap_shape] at spRun
  obtain ⟨capValue, capPost, capRead, capTyped, capRun, capPostEq⟩ :=
    Input.CallNormal.declaration_normal_entry first spPost "cap" .one (frameLoad 232#64) afterCap value spRun
  have capMapped := Input.load_one_mapped first (frameAddress 232#64) (frame + 232#64) capValue (address_read first frame 232#64 ev) capRead
  have capActual := frame_read first frame 232#64 capacity ev capMapped capCell
  have capEq : capValue = .val (.word capacity) := Option.some.inj (capRead.symm.trans capActual)
  subst capValue
  have spLocal : (entered source sp capacity).locals.lookup (ofString "sp") = some (.val (.word sp)) :=
    (bind_lookup_other _ "cap" "sp" _ (by decide)).trans (bind_lookup_same _ _ _)
  have capLocal : (entered source sp capacity).locals.lookup (ofString "cap") = some (.val (.word capacity)) := bind_lookup_same _ _ _
  have growthRun := no_growth (entered source sp capacity) sp capacity spLocal capLocal room
  have overflowRun := no_overflow (entered source sp capacity) sp capacity spLocal room bounded
  change evaluateHOLFiniteState (entered source sp capacity) afterCap = (some (.returned value), capPost) at capRun
  rw [growth_shape,
    WitnessRadix.StateSteps.next_sequence (entered source sp capacity) (entered source sp capacity) growth _ growthRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence (entered source sp capacity) (entered source sp capacity) overflow writes overflowRun (Nat.le_refl _)] at capRun
  refine ⟨capPost, spMapped, capMapped, capRun, ?_⟩
  rw [spPostEq, capPostEq]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.non_growth_entry
