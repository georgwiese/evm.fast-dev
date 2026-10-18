import InitECandidate.Solver.GasBudget.JournalInactive
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def snapshotBody : ProgHOL 64 := match Guest.guestFn_state_snapshot with | .function fn => progToHOL fn.body | _ => .skip

theorem snapshot_shape : snapshotBody = .return countVar := by
  simp only [snapshotBody, Guest.guestFn_state_snapshot, progToHOL, expToHOL, countVar]

theorem snapshot_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (code : source.code.lookup (ofString "state_snapshot") = some ([], snapshotBody, .one))
    (name : String) (continuation : ProgHOL 64) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "state_snapshot") [] continuation) =
      (let result := evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name count) continuation
       (result.1, restore source name result.2)) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "state_snapshot") [] = some (snapshotBody, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "state_snapshot") [] snapshotBody (fun _ => none) .one raw
  let entry := callEntryStateHOLFinite source callee
  have entryCounter : entry.globals.lookup (ofString "journal_n") = some (.val (.word count)) := counter
  have run : evaluateHOLFiniteState entry snapshotBody = (some (.returned (.val (.word count))), emptyLocalsHOLFinite entry) := by
    rw [snapshot_shape]
    simp [evaluateHOLFiniteState_return, countVar, evalHOLExact, toExact, entryCounter, shapeOfHOLExact]
  have frame : emptyLocalsHOLFinite (emptyLocalsHOLFinite entry) = emptyLocalsHOLFinite {source with clock := source.clock - 1 - 0} := rfl
  have actual := Input.CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "state_snapshot") [] [] snapshotBody continuation callee count 0 rfl called enough run frame
  simpa only [Nat.sub_zero] using actual

/-- A snapshot's actual saved local is precisely the current journal counter;
no snapshot value, source-clock allowance or callee result is assumed. -/
theorem snapshot_normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (code : source.code.lookup (ofString "state_snapshot") = some ([], snapshotBody, .one))
    (name : String) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "state_snapshot") [] continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ ∃ finish,
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name count) continuation = (some (.returned value), finish) ∧
      post = restore source name finish := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "state_snapshot") [] continuation value normal
  have actual := snapshot_execute source count counter code name continuation positive
  rw [actual] at normal
  let entry := bind {source with clock := source.clock - 1} name count
  let finish := (evaluateHOLFiniteState entry continuation).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entry continuation).1 = some (.returned value) at result
  have frame := congrArg Prod.snd normal
  exact ⟨positive, finish, Prod.ext result rfl, frame.symm⟩

theorem Image.empty {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base : Nat) (entries : Nat → Entry ι) : Image source objects base 0 entries := by
  constructor <;> intro index impossible <;> omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.snapshot_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.snapshot_execute
#print axioms InitECandidate.Solver.GasBudget.Journal.snapshot_normal_entry
#print axioms InitECandidate.Solver.GasBudget.Journal.Image.empty
