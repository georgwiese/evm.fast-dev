import InitECandidate.Solver.Input.CurrentTable.Set.Locals
import InitECandidate.Solver.Input.CurrentTable.Set.Guards
import InitECandidate.Solver.Input.CurrentTable.Compare
import InitECandidate.Solver.Input.CurrentTable.ImageFacts

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

noncomputable local instance : DecidableEq KeyBits.Key := Classical.decEq _

def keysEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) := bind source "keys" (New.keysPointer table)

theorem keys_setup {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))) :
    evaluateHOLFiniteState source afterLeaf =
      let output := evaluateHOLFiniteState (keysEntry source table) afterKeys
      (output.1,restore source "keys" output.2) := by
  have read := FindLeaf.header_read source table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned
    (by decide) (by decide) tableCell image.keysCell
  rw [entry_shapes.2.2.2.1]
  exact ScalarScope.declare_execute source _ "keys" _ (New.keysPointer table) afterKeys _ read rfl

theorem after_keys_nonempty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (leaf : BitVec 64)
    (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word leaf))) (nonzero : leaf ≠ 0#64) :
    evaluateHOLFiniteState source afterKeys = evaluateHOLFiniteState source compareCall := by
  rw [entry_shapes.2.2.2.2.1,guard_shapes.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,localVar,leafCell,wordCmpHOL,nonzero,evaluateHOLFiniteState_skip]

theorem comparison_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value leaf : BitVec 64}
    (data : LookupLocals source table pointer value leaf) :
    evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) compareArguments =
      some [.val (.word (slot (New.keysPointer table) leaf 32)),.val (.word pointer),.val (.word 32#64)] := by
  simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.keysCell,data.leafCell,
    data.locals.keyCell,data.locals.lengthCell,data.locals.strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,slot]

/-- A real nonempty leaf continues past the actual empty guard and compares
its stored physical key. No guessed boolean comparison result is supplied. -/
theorem comparison_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value leaf : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : Locals source table pointer value)
    (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word leaf)))
    (member : valid leaf) (marked : bits leaf = 256)
    (view : FirstDiff.ByteView source pointer query) (queryFits : pointer.toNat+32 < 2^64) (little : source.be = false)
    (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterLeaf = (outcome,post)) :
    (source.clock-post.clock ≤ 5 ∧ ∀ returned,outcome ≠ some (.returned returned)) ∨
      ∃ target inner,LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 5 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry (keysEntry source table) target "eq"
          (.val (.word (if keys leaf = query then 1#64 else 0#64)))) afterCompare = (outcome,inner) ∧
        post = restore source "keys" (restore (keysEntry source table) "eq" inner) := by
  let selected := keysEntry source table
  have current : LookupLocals selected table pointer value leaf := LookupLocals.after_keys locals leafCell
  have currentImage : Image selected table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  have fits := image.key_fits leaf member
  rw [keys_setup image locals.tableCell] at run
  change (let output := evaluateHOLFiniteState selected afterKeys;(output.1,restore source "keys" output.2)) = (outcome,post) at run
  rw [after_keys_nonempty selected leaf current.leafCell (image.routing.nonzero leaf member)] at run
  let output := evaluateHOLFiniteState selected compareCall
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  change restore source "keys" output.2 = post at endpoint
  have actual : evaluateHOLFiniteState selected compareCall = (outcome,output.2) := Prod.ext observed rfl
  rw [guard_shapes.2.2.2.2.2] at actual
  rcases Compare.scoped_trace selected output.2 (slot (New.keysPointer table) leaf 32) pointer (keys leaf) query
    (currentImage.leafKeys leaf member marked) (view.of_frame rfl) fits queryFits little installed "eq" compareArguments afterCompare
    (comparison_arguments current) outcome actual with stopped | reached
  · have clock : post.clock = output.2.clock := by rw [←endpoint]; rfl
    exact Or.inl ⟨by rw [clock]; exact stopped.1,stopped.2⟩
  · obtain ⟨target,inner,frame,forward,cost,continued,restored⟩ := reached
    exact Or.inr ⟨target,inner,frame,forward,cost,continued,by rw [←endpoint,restored]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.keys_setup
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.comparison_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.comparison_trace
