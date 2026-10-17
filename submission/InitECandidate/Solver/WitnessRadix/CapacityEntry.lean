import InitECandidate.Solver.WitnessRadix.CapacityBound
import InitECandidate.Solver.WitnessRadix.BuildEntry

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def allocatedTail : ProgHOL 64 := .decCall (ofString "t") .one (ofString "htab_new")
  [.const 32#64, localVar "cap"] tableTail

/-- Execute the literal initial cap declaration and complete actual doubling
loop, exposing the real table-allocation continuation with its chosen cap. -/
theorem capacity_entry {F : Type} (source : PanSemStateFiniteExact 64 F) (count : Nat) (small : count < 2 ^ 31)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (enough : 30 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ paid capacity : Nat,
      evaluateHOLFiniteState source body =
        (let output := evaluateHOLFiniteState target allocatedTail; (output.1, restore source "cap" output.2)) ∧
      paid ≤ 30 ∧ 2 * count + 2 ≤ capacity ∧ capacity ≤ 4 * count + 4 ∧ capacity ≤ 2 ^ 32 ∧
      (capacity = 4 ∨ capacity % 8 = 0) ∧
      target.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with clock := source.clock - paid } ∧
      (∀ name : MlS, ofString "cap" ≠ name → target.locals.lookup name = source.locals.lookup name) := by
  let initial := bind source "cap" 4#64
  have initialCount : initial.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) :=
    (bind_lookup_other source "cap" "n" _ (by decide)).trans countLocal
  have initialCap : initial.locals.lookup (ofString "cap") = some (.val (.word 4#64)) := bind_lookup_same _ _ _
  obtain ⟨target, paid, capacity, loopRun, budget, sufficient, capBound, capTop, shape, capLocal, frame, others⟩ :=
    Capacity.bounded initial count small initialCount initialCap enough
  have clock : target.clock = source.clock - paid := congrArg (fun state => state.clock) frame
  have finalFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
    rw [frame]
    rfl
  have coreRun := StateSteps.next_sequence initial target capacityLoop allocatedTail loopRun
    (by change target.clock ≤ source.clock; omega)
  have setup : BuildEntry.Initializes source [("cap", .const 4#64)] initial
      (fun output => restore source "cap" output) := .step 4#64 rfl (.done _)
  have scope := BuildEntry.declarations_execute setup (.seq capacityLoop allocatedTail)
  rw [coreRun] at scope
  refine ⟨target, paid, capacity, ?_, budget, sufficient, capBound, capTop, shape, capLocal, finalFrame, ?_⟩
  · rw [body_shape]
    exact scope
  · intro name different
    rw [others name different]
    simp [initial, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.capacity_entry
