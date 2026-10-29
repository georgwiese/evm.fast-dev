import InitECandidate.Solver.Input.CurrentTable.NewScalarContext

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Normal construction tails return the real header and protect every
word before it, at the actual live allocator cursor. -/
def ScalarTail (cap stride : BitVec 64) (program : ProgHOL 64) : Prop :=
  ∀ source post table cursor,ScalarContext source table cursor cap stride → ∀ value,
    evaluateHOLFiniteState source program=(some (.returned value),post) →
    value=.val (.word table) ∧ PersistentNormalFrame source post table

theorem ScalarTail.allocated (cap stride amount : BitVec 64) (name : String) (offset : Nat)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (notTable : ofString name≠ofString "t") (notCap : ofString name≠ofString "ncap") (notStride : ofString name≠ofString "stride")
    (inside : offset<88) (aligned : offset%8=0)
    (reads : ∀ source table cursor,ScalarContext source table cursor cap stride →
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (tail : ScalarTail cap stride continuation) :
    ScalarTail cap stride (.decCall (ofString name) .one (ofString "alloc") arguments
      (.seq (.store (Scalar.plus (localVar "t") offset) (localVar name)) continuation)) := by
  intro source post table cursor context value normal
  rcases array_allocation_trace source post table cursor amount name offset arguments continuation notTable inside aligned
      context.arena.domain context.tableArena context.tableAligned context.tableCell (reads source table cursor context) context.arena.code
      context.heapCell context.cursorBound _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=arrayEntry source table cursor amount name offset
    have first:=array_persistent_frame source table cursor amount table name offset context.tableArena inside context.cursorArena room (Nat.le_refl _) context.tableBefore
    have current:=context.after_array amount name offset notTable notCap notStride inside room
    obtain ⟨valueEq,last⟩:=tail ready inner table (PersistentAlloc.rounded cursor amount) current value continued
    have total:=first.trans source ready inner table table last (Nat.le_refl _)
    exact ⟨valueEq,total.of_erase source inner source post table rfl (by rw [endpoint]; rfl)⟩

/-- All three actual array allocations and seven remaining metadata fields
have the same earlier-input/runtime frame for arbitrary scalar key stride.
Every allocation derives its own room from the actual normal execution. -/
theorem scalar_arrays_frame (cap stride : BitVec 64) : ScalarTail cap stride keysCall := by
  rw [array_shapes.1]
  apply ScalarTail.allocated cap stride ((cap+1#64)*stride) "keys" 32 [keyAmount] nodesCall
    (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro source table cursor context
    simp [keyAmount,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
      context.capCell,context.strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  · rw [array_shapes.2.1]
    apply ScalarTail.allocated cap stride (size32 cap) "nodes" 40 [nodeAmount] orderCall
      (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro source table cursor context
      simp [nodeAmount,size32,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
        context.capCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
    · rw [array_shapes.2.2]
      apply ScalarTail.allocated cap stride (size8 cap) "order" 48 [orderAmount] finalFields
        (by decide) (by decide) (by decide) (by decide) (by decide)
      · intro source table cursor context
        simp [orderAmount,size8,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
          context.capCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
      · exact fun source post table cursor context value normal=>scalar_final_frame source post table cursor cap stride context value normal

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.ScalarTail.allocated
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_arrays_frame
