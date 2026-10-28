import InitECandidate.Solver.Input.CurrentTable.Get.ReadOnly
import InitECandidate.Solver.Input.CurrentTable.Get.TailCost
import InitECandidate.Solver.Input.CurrentTable.Get.CompareReturned
import InitECandidate.Solver.Input.ReturnFactsScoped

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem after_empty_returned {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (member : valid leaf) (marked : bits leaf=256) (installed : OriginalCode.Installed source.code) :
    ReturnFacts.Returns source afterEmpty (Result ValueOf) := by
  have selectedImage : Image (prepared source table) table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  have selectedTable := (prepared_keeps source table "t" (by decide) (by decide) (by decide)).trans tableCell
  have selectedLeaf := (prepared_keeps source table "leaf" (by decide) (by decide) (by decide)).trans leafCell
  have tail : ReturnFacts.Returns (prepared source table) compareCall (Result ValueOf) := by
    apply ReturnFacts.scoped_readonly (prepared source table) "eq" .one (ofString "memeq") compareArguments
      Memeq32.formals Memeq32.body afterCompare .one (MutableTable.MemeqAny.original_code source.code installed)
      (MutableTable.MemeqAny.readonly source.code) (Result ValueOf)
    intro target answer frame
    let current := CallNormal.continuationEntry (prepared source table) target "eq" answer
    have currentImage : Image current table cap root next count valid bits left right keys ValueOf := selectedImage.of_frame frame
    have currentTable := (CallNormal.continuation_lookup_other (prepared source table) target "eq" "t" answer (by decide)).trans selectedTable
    have currentLeaf := (CallNormal.continuation_lookup_other (prepared source table) target "eq" "leaf" answer (by decide)).trans selectedLeaf
    exact after_compare_returned currentImage currentTable currentLeaf member marked
  intro post value normal
  rw [setup image tableCell] at normal
  have observed := congrArg Prod.fst normal
  change (evaluateHOLFiniteState (prepared source table) compareCall).1=some (.returned value) at observed
  have innerRun : evaluateHOLFiniteState (prepared source table) compareCall=
      (some (.returned value),(evaluateHOLFiniteState (prepared source table) compareCall).2) := Prod.ext observed rfl
  exact tail _ value innerRun

/-- A real original lookup return is exactly absent or contains a value
from an actual selected leaf. The full physical input/table frame is retained.
The incoming query may be unaligned, unreadable or arbitrary. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Result ValueOf value ∧ LocalEffects.erase post=LocalEffects.erase source := by
  have physical := body_readonly source.code installed source rfl
  rw [run] at physical
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) lookupArguments=
      some [.val (.word table),.val (.word pointer)] := by
    simp [lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,tableCell,keyCell]
  rw [body_shape] at run
  obtain ⟨target,leaf,inner,found,frame,forward,cost,continued,endpoint⟩ :=
    FindLeaf.scoped_returned source post table pointer (New.nodesPointer table cap) root valid bits left right image.lookup_context installed
      "leaf" lookupArguments afterLeaf args value run
  let current := CallNormal.continuationEntry source target "leaf" (.val (.word leaf))
  have currentImage : Image current table cap root next count valid bits left right keys ValueOf := image.of_frame frame
  have currentTable := (CallNormal.continuation_lookup_other source target "leaf" "t" (.val (.word leaf)) (by decide)).trans tableCell
  have currentLeaf := CallNormal.continuation_lookup_same source target "leaf" (.val (.word leaf))
  have currentCode : OriginalCode.Installed current.code := by rw [LocalEffects.code_of_erase source current frame]; exact installed
  refine ⟨?_,physical⟩
  rcases found with zero|⟨member,marked⟩
  · subst leaf
    rw [after_leaf_empty current currentLeaf] at continued
    exact absent_returned current ValueOf inner value continued
  · rw [after_leaf_nonempty current leaf currentLeaf (image.routing.nonzero leaf member)] at continued
    exact after_empty_returned currentImage currentTable currentLeaf member marked currentCode inner value continued

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.after_empty_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.body_returned
