import InitECandidate.Solver.Input.PayloadHashTransactionCost
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real transaction hash/counter body preserves any protected input
word below its roots array, independently of row or digest values. -/
theorem step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros query : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n)
    (protection : SszHash.Protected source stp accel chunk zeros query) (below : query.toNat<roots.toNat)
    (run : evaluateHOLFiniteState source transactionStep=(none,post)) : post.memory query=source.memory query := by
  rw [loop_shapes.2.1] at run
  obtain ⟨middle,called,advanced⟩ := sequence_none source post _ increment run
  obtain ⟨outArena,temporary⟩ := call_geometry array roots cursor stp accel chunk pointers lengths n capacity index geometry active
  have rootsAway := CopyGeneral.Away.after roots query (32*n) geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) below
  have cursorBelow : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  have front := PBytes.call_memory source middle (pointers index) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros query (lengths index)
    (by have a:=geometry.lengthsBound index active; have b:=geometry.capacityBound; omega) protection actual.heap (geometry.inputs index active) temporary geometry.aligned outArena cursorBelow
    (CopyGeneral.Away.subrange roots query (32*n) (32*index) 32 rootsAway (by omega)) transactionArguments
    (arguments_read source array roots cursor stp accel chunk zeros pointers lengths n capacity index actual geometry active) called
  have tail := MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change (evaluateHOLFiniteState middle increment).2.memory query=middle.memory query at tail
  rw [advanced] at tail
  exact tail.trans front

/-- Same normal transaction-loop execution derives its real bounded index,
all decoded rows, original workspace and restored temporary heap at exit. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (inside : index≤n) (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity)
    (run : evaluateHOLFiniteState source transactionLoop=(none,post)) : valid array roots cursor stp accel chunk zeros pointers lengths n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid array roots cursor stp accel chunk zeros pointers lengths n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) transactionTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,target) → valid array roots cursor stp accel chunk zeros pointers lengths n target := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,currentRound⟩ := ready
    have active := active_of_test current array roots cursor stp accel chunk zeros pointers lengths n position geometry.countBound positionBound currentRound word read nonzero
    have next := step_normal (decClockHOLFinite current) target array roots cursor stp accel chunk zeros pointers lengths n capacity position
      (RoundState.dec_clock current array roots cursor stp accel chunk zeros pointers lengths n position currentRound) geometry active bodyRun
    exact ⟨position+1,by omega,next⟩
  rw [loop_shapes.1] at run
  exact loop_invariant source.code (ofString "txs") transactionTest transactionStep (transaction_step_local (ofString "txs") (by decide))
    (valid array roots cursor stp accel chunk zeros pointers lengths n) transition source post rfl ⟨index,inside,actual⟩ run

/-- Whole original transaction loop preserves protected decoded/input words
on a genuine normal exit, with no assumption about future hash success. -/
theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros query : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (inside : index≤n) (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity)
    (protection : SszHash.Protected source stp accel chunk zeros query) (below : query.toNat<roots.toNat)
    (run : evaluateHOLFiniteState source transactionLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>valid array roots cursor stp accel chunk zeros pointers lengths n current ∧ SszHash.Protected current stp accel chunk zeros query
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) transactionTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,target) → invariant target ∧ target.memory query=current.memory query := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨⟨position,positionBound,currentRound⟩,currentProtection⟩ := ready
    have active := active_of_test current array roots cursor stp accel chunk zeros pointers lengths n position geometry.countBound positionBound currentRound word read nonzero
    have entryRound := RoundState.dec_clock current array roots cursor stp accel chunk zeros pointers lengths n position currentRound
    have entryProtection := currentProtection.with_workspace current (decClockHOLFinite current) stp accel chunk zeros query entryRound.workspace
    have next := step_normal (decClockHOLFinite current) target array roots cursor stp accel chunk zeros pointers lengths n capacity position entryRound geometry active bodyRun
    have nextProtection := currentProtection.with_workspace current target stp accel chunk zeros query next.workspace
    have memory := step_memory (decClockHOLFinite current) target array roots cursor stp accel chunk zeros query pointers lengths n capacity position entryRound geometry active entryProtection below bodyRun
    exact ⟨⟨⟨position+1,by omega,next⟩,nextProtection⟩,memory⟩
  rw [loop_shapes.1] at run
  exact MemoryAt.loop_normal source.code (ofString "txs") transactionTest transactionStep query
    (fun current=>(transaction_step_local (ofString "txs") (by decide)).summary_full current) invariant transition source post rfl ⟨⟨index,inside,actual⟩,protection⟩ run

theorem loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code transactionLoop := by
  rw [loop_shapes.1]
  exact GlobalEffects.loop key code _ _ (transaction_step_globals key code installed different)

theorem loop_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key transactionLoop := by
  rw [loop_shapes.1]
  exact .loop transactionTest (transaction_step_local key different)

end InitECandidate.Solver.Input.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.step_memory
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.loop_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.loop_memory
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.loop_globals
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.loop_local
