import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionCost

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros query : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n)) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source transactionStep=(none,post)) : post.memory query=source.memory query := by
  rw [loop_shapes.2.1] at actual
  obtain ⟨middle,normal,advanced⟩ := Input.sequence_none source post _ increment actual
  have frame := call_frame source middle array roots cursor chunk zeros query pointers lengths n capacity index data geometry active below rootsAway chunkAway normal
  have current := call_normal source middle array roots cursor chunk zeros pointers lengths n capacity index data geometry active normal
  have read : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,current.position,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have endpoint := assign_none middle post "i" _ (BitVec.ofNat 64 (index+1)) read advanced
  rw [endpoint]
  exact frame.1

/-- Every actual normal transaction iteration retains arbitrary protected
caller metadata, the complete physical row image and the real entering heap. -/
theorem loop_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros query : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (inside : index≤n)
    (below : query.toNat<cursor.toNat) (rootsAway : CopyGeneral.Away roots query (32*n)) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source transactionLoop=(none,post)) :
    post.memory query=source.memory query ∧ valid array roots cursor chunk zeros pointers lengths n post := by
  let invariant (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    ∃ position, position≤n ∧ RoundState state array roots cursor chunk zeros pointers lengths n position ∧ state.memory query=source.memory query
  have final : invariant post := by
    rw [loop_shapes.1] at actual
    apply loop_invariant_no_control source.code transactionTest transactionStep
      (fun current=>((transaction_step_local (ofString "ntx") (by decide)).summary_full current).2.2)
      invariant _ source post rfl ⟨index,inside,data,rfl⟩ actual
    intro current codeEq ready word read nonzero funded target continued
    obtain ⟨position,positionBound,currentData,kept⟩ := ready
    have active := active_of_test current array roots cursor chunk zeros pointers lengths n position geometry.countBound positionBound currentData word read nonzero
    have frame := step_memory (decClockHOLFinite current) target array roots cursor chunk zeros query pointers lengths n capacity position
      currentData.dec_clock geometry active below rootsAway chunkAway continued
    have next := step_normal (decClockHOLFinite current) target array roots cursor chunk zeros pointers lengths n capacity position currentData.dec_clock geometry active continued
    exact ⟨position+1,by omega,next,frame.trans kept⟩
  obtain ⟨position,positionBound,data,kept⟩ := final
  exact ⟨kept,position,positionBound,data⟩

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.step_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.loop_frame
