import InitECandidate.Solver.GasBudget.JournalAppendStores

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def increment : ProgHOL 64 := .assign .global (ofString "journal_n") (.op .add [countVar, .const 1#64])
def mutateSet : ProgHOL 64 := .call (some (none, none)) (ofString "htab_set") [localVar "t", localVar "key", localVar "value"]
def mutateDelete : ProgHOL 64 := .call (some (none, none)) (ofString "htab_del") [localVar "t", localVar "key"]

theorem set_tail_shape : afterStores setAfterCopy = .seq increment (.seq mutateSet (.return (.const 0#64))) := by
  simp only [afterStores, setAfterCopy, setAfterGuard, setAfterGet, setBody, Guest.guestFn_jset, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, increment, mutateSet, countVar, localVar]

theorem delete_tail_shape : afterStores deleteAfterCopy = .seq increment (.seq mutateDelete (.return (.const 0#64))) := by
  simp only [afterStores, deleteAfterCopy, deleteAfterGuard, deleteAfterEmpty, deleteAfterGet, deleteBody, Guest.guestFn_jdel, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, increment, mutateDelete, countVar, localVar]

theorem increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    evaluateHOLFiniteState source increment = (none, Input.putGlobal source "journal_n" (count + 1#64)) := by
  apply Input.global_assign_execute source "journal_n" count (count + 1#64) _ counter
  simp [eval, countVar, evalHOLExact, evalListHOLExact, toExact, counter, valueIsWord, valueWord, wordOpHOL, wordOp]

/-- Passing the actual unsigned cap guard prevents increment wraparound. -/
theorem increment_progress (count cap : BitVec 64) (room : count.toNat < cap.toNat) :
    (count + 1#64).toNat = count.toNat + 1 ∧ (count + 1#64).toNat ≤ cap.toNat := by
  have capSmall := cap.isLt
  rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]
  change count.toNat + 1 = count.toNat + 1 ∧ count.toNat + 1 ≤ cap.toNat
  omega

theorem increment_models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source cursor objects) (count : BitVec 64) :
    TableFamily.Model (Input.putGlobal source "journal_n" (count + 1#64)) cursor objects :=
  family.of_control (Input.putGlobal.lookup_other source "journal_n" _ (ofString "heap_ptr") (by decide)) rfl rfl rfl

theorem increment_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base count : Nat) (entries : Nat → Entry ι) (image : Image source objects base count entries) (word : BitVec 64) :
    Image (Input.putGlobal source "journal_n" (word + 1#64)) objects base count entries :=
  image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_tail_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_tail_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.increment_execute
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.increment_progress
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.increment_models
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.increment_image
