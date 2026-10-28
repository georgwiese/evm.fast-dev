import InitECandidate.Solver.Input.CurrentTable.Get.Program
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def lengthEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "klen" 32#64
def strideEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (lengthEntry source) "stride" 32#64
def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) := bind (strideEntry source) "keys" (New.keysPointer table)
def restorePrepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "klen" (restore (lengthEntry source) "stride" (restore (strideEntry source) "keys" post))

theorem prepared_keeps (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (name : String)
    (notLength : ofString "klen"≠ofString name) (notStride : ofString "stride"≠ofString name) (notKeys : ofString "keys"≠ofString name) :
    (prepared source table).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other (strideEntry source) "keys" name (New.keysPointer table) notKeys).trans
    ((bind_lookup_other (lengthEntry source) "stride" name 32#64 notStride).trans (bind_lookup_other source "klen" name 32#64 notLength))

/-- These are the actual three lexical table-header loads before memeq,
with every original restoration retained on every subsequent outcome. -/
theorem setup {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    evaluateHOLFiniteState source afterEmpty=
      let output:=evaluateHOLFiniteState (prepared source table) compareCall
      (output.1,restorePrepared source output.2) := by
  have lengthRead := FindLeaf.header_read source table 32#64 0 image.domain image.geometry.table image.aligned
    (by decide) (by decide) tableCell (by simpa only [BitVec.add_zero] using image.keyLength)
  have firstTable := (bind_lookup_other source "klen" "t" 32#64 (by decide)).trans tableCell
  have strideRead := FindLeaf.header_read (lengthEntry source) table 32#64 8 image.domain image.geometry.table image.aligned
    (by decide) (by decide) firstTable image.stride
  have secondTable := (bind_lookup_other (lengthEntry source) "stride" "t" 32#64 (by decide)).trans firstTable
  have keysRead := FindLeaf.header_read (strideEntry source) table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned
    (by decide) (by decide) secondTable image.keysCell
  let output := evaluateHOLFiniteState (prepared source table) compareCall
  have third : evaluateHOLFiniteState (strideEntry source) afterStride=(output.1,restore (strideEntry source) "keys" output.2) :=
    ScalarScope.declare_execute _ _ "keys" (.load .one (header 32)) (New.keysPointer table) compareCall output.1 keysRead rfl
  have second : evaluateHOLFiniteState (lengthEntry source) afterLength=
      (output.1,restore (lengthEntry source) "stride" (restore (strideEntry source) "keys" output.2)) :=
    ScalarScope.declare_execute _ _ "stride" (.load .one (header 8)) 32#64 afterStride output.1 strideRead third
  exact ScalarScope.declare_execute source _ "klen" (.load .one (header 0)) 32#64 afterLength output.1 lengthRead second

/-- Actual prepared lookup operands always contain the literal32-byte
length; key mapping and future comparison success are not premises. -/
theorem compare_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table pointer leaf : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf))) :
    evalListHOLFinite (prepared source table) (h:=fun query=>Classical.propDecidable ((prepared source table).memaddrs query)) compareArguments=
      some [.val (.word (slot (New.keysPointer table) leaf 32)),.val (.word pointer),.val (.word 32#64)] := by
  have key := (prepared_keeps source table "key" (by decide) (by decide) (by decide)).trans keyCell
  have leaf := (prepared_keeps source table "leaf" (by decide) (by decide) (by decide)).trans leafCell
  have keys : (prepared source table).locals.lookup (ofString "keys")=some (.val (.word (New.keysPointer table))) := bind_lookup_same _ _ _
  have stride : (prepared source table).locals.lookup (ofString "stride")=some (.val (.word 32#64)) :=
    (bind_lookup_other (strideEntry source) "keys" "stride" _ (by decide)).trans (bind_lookup_same _ _ _)
  have length : (prepared source table).locals.lookup (ofString "klen")=some (.val (.word 32#64)) :=
    (bind_lookup_other (strideEntry source) "keys" "klen" _ (by decide)).trans
      ((bind_lookup_other (lengthEntry source) "stride" "klen" _ (by decide)).trans (bind_lookup_same _ _ _))
  simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,key,leaf,keys,stride,length,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,slot]

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.setup
#print axioms InitECandidate.Solver.Input.CurrentTable.Get.compare_arguments
