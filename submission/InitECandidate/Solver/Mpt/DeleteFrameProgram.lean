import InitECandidate.Solver.Mpt.DeleteBodyProgram
import InitECandidate.Solver.Mpt.LocalFieldStores

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | extension | branch
def Kind.name : Kind→String | .extension=>"fr" | .branch=>"fr2"
def Kind.tag : Kind→BitVec 64 | .extension=>2#64 | .branch=>3#64
def Kind.push : Kind→ProgHOL 64 | .extension=>DeleteBody.extensionPush | .branch=>DeleteBody.branchPush
def Kind.call : Kind→ProgHOL 64 | .extension=>DeleteBody.extensionFrameScope | .branch=>DeleteBody.branchFrameScope
def Kind.fields : Kind→(String→BitVec 64)→List LocalFields.Field
  | .extension,words=>[⟨0,.saved "top" (words "top")⟩,⟨8,.saved "node" (words "node")⟩,
      ⟨16,.literal 2#64⟩,⟨24,.saved "seg" (words "seg")⟩,⟨32,.saved "sl" (words "sl")⟩]
  | .branch,words=>[⟨0,.saved "top" (words "top")⟩,⟨8,.saved "node" (words "node")⟩,
      ⟨16,.literal 3#64⟩,⟨32,.saved "idx" (words "idx")⟩]
def Kind.advance : Kind→ProgHOL 64
  | .extension=>.seq (.assign .local (ofString "top") (localVar "fr"))
      (.seq (.assign .local (ofString "node") (DeleteBody.field "node" 48#64))
        (.seq (.assign .local (ofString "level") (.op .add [localVar "level",localVar "sl"]))
          (.assign .local (ofString "go") (.const 1#64))))
  | .branch=>.seq (.assign .local (ofString "top") (localVar "fr2"))
      (.seq (.assign .local (ofString "node") (.load .one (DeleteBody.childAddress "node" (localVar "idx"))))
        (.seq (.assign .local (ofString "level") (.op .add [localVar "level",.const 1#64]))
          (.assign .local (ofString "go") (.const 1#64))))

theorem Kind.call_shape (kind : Kind) :
    kind.call=.decCall (ofString kind.name) .one (ofString "scratch_alloc") [.const 40#64] kind.push := by
  cases kind with
  | extension=>simpa only [Kind.call,Kind.name,Kind.push] using DeleteBody.extension_shapes.2.2.2.2
  | branch=>simpa only [Kind.call,Kind.name,Kind.push] using DeleteBody.branch_shapes.2.2.1

theorem Kind.push_shape (kind : Kind) (words : String→BitVec 64) :
    kind.push=LocalFields.program kind.name (kind.fields words) kind.advance := by
  cases kind <;>
    simp only [Kind.push,Kind.name,Kind.fields,Kind.advance,LocalFields.program,LocalFields.address,LocalFields.Operand.expression,
      DeleteBody.extensionPush, DeleteBody.extensionFrameScope, DeleteBody.prefixChoice, DeleteBody.prefixScope, DeleteBody.afterSegment, DeleteBody.extensionBlock, DeleteBody.nonleaf, DeleteBody.kindChoice, DeleteBody.afterHash, DeleteBody.afterKind, DeleteBody.nonempty, DeleteBody.nodeChoice, DeleteBody.descentBody, DeleteBody.descent, DeleteBody.afterGo, DeleteBody.afterResult, DeleteBody.afterTop, DeleteBody.body, DeleteBody.branchPush, DeleteBody.branchFrameScope, DeleteBody.branchIndexScope, DeleteBody.branchBlock,DeleteBody.field,DeleteBody.childAddress,
      Guest.guestFn__mpt_delete_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar,addConst]

theorem Kind.geometry (kind : Kind) (words : String→BitVec 64) :
    ∀ field∈kind.fields words,field.offset+8≤40 ∧ field.offset%8=0 := by
  cases kind <;> simp [Kind.fields]

theorem Kind.fields_distinct (kind : Kind) (words : String→BitVec 64) (record : BitVec 64) :
    ((LocalFields.writes record (kind.fields words)).map Prod.fst).Nodup := by
  have offsets : ((kind.fields words).map (fun field=>BitVec.ofNat 64 field.offset)).Nodup:=by
    cases kind <;> simp only [Kind.fields,List.map_cons,List.map_nil] <;> decide
  have injective : Function.Injective (fun offset : BitVec 64=>record+offset):=by
    intro first second same
    exact (BitVec.add_right_inj record).1 same
  simpa only [LocalFields.writes,List.map_map,Function.comp_def] using offsets.map injective

/-- Both literal pushes have zero source call/loop cost after the
allocator. The child and level updates are the original expressions. -/
theorem Kind.push_quiet (kind : Kind) (code) : Input.QuietClock.Preserves code kind.push := by
  rw [kind.push_shape (fun _=>0#64)]
  apply LocalFields.quiet
  cases kind <;>
    exact Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _)
      (Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _)
        (Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _)
          (Input.QuietClock.assign code _ _)))

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.call_shape
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.push_shape
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.geometry
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.fields_distinct
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.Kind.push_quiet
