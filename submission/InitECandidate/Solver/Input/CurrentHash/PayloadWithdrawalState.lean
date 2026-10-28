import InitECandidate.Solver.Input.CurrentHash.PayloadWithdrawalMemory
import InitECandidate.Solver.Input.CurrentHash.PayloadStateRelease
import InitECandidate.Solver.Input.CurrentHash.PayloadDynamicList

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem withdrawal_loop_globals (cursorKey : Cursor) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves (key cursorKey) code withdrawalLoop := by
  rw [loop_shapes.2.2.1]
  apply GlobalEffects.loop
  rw [loop_shapes.2.2.2]
  exact GlobalEffects.sequence _ code _ _ (Effects.call_preserves cursorKey code installed .htr_withdrawal (some none) withdrawalArguments)
    (GlobalEffects.assign _ code _ _)

/-- The actual current withdrawal loop carries the complete earlier payload
image to its next list call. Its real normal iterations supply the restored
heap; none of the later list/hash returns is assumed. -/
theorem State.after_withdrawal_loop {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (p roots : BitVec 64) (n index : Nat)
    (round : Withdrawals.RoundState source p roots n index) (bounded : n≤134217728) (inside : index≤n)
    (inputArena : AllocatedBytes.Arena p (44*n)) (rootsArena : AllocatedBytes.Arena roots (32*n)) (rootsAligned : roots.toNat%8=0) (rootsAfter : ch.toNat≤roots.toNat)
    (actual : evaluateHOLFiniteState source withdrawalLoop=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size ∧ Withdrawals.valid p roots n post := by
  have frame (query : BitVec 64) (before : query.toNat<ch.toNat) := Withdrawals.loop_frame source post p roots cursor zeros query n index
    (data.query_context query before) round bounded inside inputArena rootsArena
    (CopyGeneral.Away.after roots query (32*n) rootsAligned (by have h:=rootsArena.upper; omega) (by omega)) actual
  have atRecord := frame record (by have h:=data.afterRecord; omega)
  have globals := withdrawal_loop_globals .lengthChunk source.code data.context.installed source rfl
  rw [actual] at globals
  have kept (name : String) (different : ofString name≠ofString "i") : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have summary := (LocalPrefix.loop withdrawalTest (withdrawal_step_local (ofString name) different)).summary_full source
    unfold LocalSummary at summary
    rw [←loop_shapes.2.2.1,actual] at summary
    exact summary.1 rfl
  refine ⟨?_,atRecord.2.2⟩
  exact data.with_context cursor atRecord.2.1 data.afterChunks (by intro query lower before; exact (frame query before).1)
    ((kept "pl" (by decide)).trans data.payload) ((kept "raw" (by decide)).trans data.raw) ((kept "ch" (by decide)).trans data.chunks)
    ((kept "out" (by decide)).trans data.output) ((congrArg Prod.snd globals).trans data.chunkCell)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.withdrawal_loop_globals
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_withdrawal_loop
