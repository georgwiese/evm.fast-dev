import InitECandidate.Solver.Input.CurrentTable.Set.ComparisonEntry
import InitECandidate.Solver.Input.CurrentTable.Set.SeekTrace
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Call

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

noncomputable local instance : DecidableEq KeyBits.Key := Classical.decEq _

def differenceArguments : List (ExpHOL 64) :=
  [localVar "key",.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "klen"]

theorem difference_shape : differenceCall = .decCall (ofString "d") .one (ofString "htab_first_diff") differenceArguments afterDifference :=
  entry_shapes.2.2.2.2.2.2

theorem after_compare_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (eqCell : source.locals.lookup (ofString "eq") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterCompare = evaluateHOLFiniteState source differenceCall := by
  rw [entry_shapes.2.2.2.2.2.1,guard_shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,localVar,eqCell,wordCmpHOL,evaluateHOLFiniteState_skip]

theorem difference_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table pointer value leaf : BitVec 64}
    (data : LookupLocals source table pointer value leaf) :
    evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) differenceArguments =
      some [.val (.word pointer),.val (.word (slot (New.keysPointer table) leaf 32)),.val (.word 32#64)] := by
  simp [differenceArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.keysCell,data.leafCell,
    data.locals.keyCell,data.locals.lengthCell,data.locals.strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,slot]

/-- The actual failed-equality continuation computes its genuine first
mismatch and runs the original second search. It either stops within546
source ticks or reaches the unchanged new-leaf call with its strict split,
parent edge and the real caller bindings needed for that allocation. -/
theorem difference_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer value leaf : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : LookupLocals source table pointer value leaf) (member : valid leaf) (marked : bits leaf = 256)
    (route : Route bits left right query root leaf) (different : keys leaf ≠ query)
    (eqCell : source.locals.lookup (ofString "eq") = some (.val (.word 0#64)))
    (view : FirstDiff.ByteView source pointer query) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCompare = (outcome,post)) :
    (source.clock-post.clock ≤ 546 ∧ ∀ returned,outcome ≠ some (.returned returned)) ∨
      ∃ entry target inner node parent,LookupLocals target table pointer value leaf ∧
        SeekState entry target (New.nodesPointer table cap) node parent pointer (KeyBits.first query (keys leaf)) ∧
        valid node ∧ KeyBits.first query (keys leaf) < bits node ∧
        Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent (KeyBits.first query (keys leaf)) ∧
        LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 546 ∧
        evaluateHOLFiniteState target newLeafCall = (outcome,inner) ∧
        post = restore source "d" (restoreSeek entry (New.nodesPointer table cap) inner) := by
  have first := KeyBits.first_spec query (keys leaf)
  have inside : KeyBits.first query (keys leaf) < 256 := by
    have bounded := first.bounded
    have notMarker : KeyBits.first query (keys leaf) ≠ 256 := by
      intro marker
      exact different ((first.marker_iff.mp marker).symm)
    omega
  rw [after_compare_zero source eqCell,difference_shape] at run
  rcases FirstDiff.scoped_trace source post pointer (slot (New.keysPointer table) leaf 32) query (keys leaf)
    view (image.leafKeys leaf member marked) installed "d" differenceArguments afterDifference (difference_arguments locals) outcome run with stopped | reached
  · exact Or.inl ⟨by have price := stopped.1; omega,stopped.2⟩
  · obtain ⟨hashed,afterPost,frame,forward,cost,continued,endpoint⟩ := reached
    let entry := CallNormal.continuationEntry source hashed "d" (.val (.word (BitVec.ofNat 64 (KeyBits.first query (keys leaf)))))
    have readyImage : Image entry table cap root next count valid bits left right keys ValueOf := image.of_frame frame
    have readyLocals : LookupLocals entry table pointer value leaf := locals.after_call hashed "d" _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have differenceCell := CallNormal.continuation_lookup_same source hashed "d" (.val (.word (BitVec.ofNat 64 (KeyBits.first query (keys leaf)))))
    have tailClock := evaluateHOLFiniteState_clock_le entry afterDifference
    change evaluateHOLFiniteState entry afterDifference = (outcome,afterPost) at continued
    rw [continued] at tailClock
    change afterPost.clock ≤ hashed.clock at tailClock
    rcases seek_trace entry afterPost table (New.nodesPointer table cap) root leaf pointer (KeyBits.first query (keys leaf))
      valid bits left right keys query readyImage.lookup_context readyImage.routing (image.root_of_member leaf member) marked route inside first
      readyLocals.locals.tableCell differenceCell readyLocals.locals.keyCell (view.of_frame frame) outcome continued with stopped | reached
    · have price : hashed.clock-afterPost.clock ≤ 257 := stopped.1
      have clock : post.clock = afterPost.clock := by rw [endpoint]; rfl
      exact Or.inl ⟨by rw [clock]; omega,stopped.2⟩
    · obtain ⟨target,inner,node,parent,state,live,strict,suffix,parentLink,kept,tailForward,tailCost,called,restored⟩ := reached
      have data : LookupLocals target table pointer value leaf := by
        refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
        · exact (kept "t" (by decide) (by decide) (by decide)).trans readyLocals.locals.tableCell
        · exact (kept "key" (by decide) (by decide) (by decide)).trans readyLocals.locals.keyCell
        · exact (kept "value" (by decide) (by decide) (by decide)).trans readyLocals.locals.valueCell
        · exact (kept "klen" (by decide) (by decide) (by decide)).trans readyLocals.locals.lengthCell
        · exact (kept "stride" (by decide) (by decide) (by decide)).trans readyLocals.locals.strideCell
        · exact (kept "leaf" (by decide) (by decide) (by decide)).trans readyLocals.leafCell
        · exact (kept "keys" (by decide) (by decide) (by decide)).trans readyLocals.keysCell
      have finalFrame : LocalEffects.erase target = LocalEffects.erase source := state.cursor.frame.trans frame
      change target.clock ≤ hashed.clock at tailForward
      change hashed.clock-target.clock ≤ 257 at tailCost
      exact Or.inr ⟨entry,target,inner,node,parent,data,state,live,strict,suffix,parentLink,finalFrame,by omega,by omega,called,
        by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.difference_arguments
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.difference_trace
