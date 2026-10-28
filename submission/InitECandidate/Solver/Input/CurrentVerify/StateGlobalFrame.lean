import InitECandidate.Solver.Input.CurrentVerify.StateContinuationTrace
import InitECandidate.Solver.Mpt.StateInitGlobals

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The complete real state initializer, including exceptional child paths,
retains every global outside its actual nine destinations. A normal main
continuation relates that same callee entry back to its saved caller. -/
theorem StateInitReturned.globals {input : Guest.InputBlob}
    {caller target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (returned : StateInitReturned input caller target pointer si boundary)
    (key : MlS) (safe : key∉Mpt.StateInitGlobals.changed) : target.globals.lookup key=caller.globals.lookup key := by
  obtain ⟨entry,value,inputs,frame,bodyRun,checked⟩:=returned
  have installed : OriginalCode.Installed entry.code := by
    obtain ⟨array,table,cap,root,codes,heap,start,length,arena,rest⟩:=inputs
    exact arena.code
  have pure:=Mpt.StateInitGlobals.preserves_state_init key entry.code installed safe entry rfl
  change GlobalEffects.erase key (evaluateHOLFiniteState entry Mpt.StateInit.body).2=GlobalEffects.erase key entry at pure
  rw [bodyRun] at pure
  have physical:=congrArg Prod.snd pure
  have saved:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.globals.lookup key) frame
  change entry.globals.lookup key=caller.globals.lookup key at saved
  exact physical.trans saved

theorem StateInitReturned.hash_globals {input : Guest.InputBlob}
    {caller target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (returned : StateInitReturned input caller target pointer si boundary) :
    target.globals.lookup (ofString "keccak_st")=caller.globals.lookup (ofString "keccak_st") ∧
      target.globals.lookup (ofString "keccak_pad")=caller.globals.lookup (ofString "keccak_pad") ∧
      target.globals.lookup (ofString "mpt_hash_scratch")=caller.globals.lookup (ofString "mpt_hash_scratch") :=
  ⟨returned.globals _ (by decide),returned.globals _ (by decide),returned.globals _ (by decide)⟩

theorem StateInitReturned.frame_cursor {input : Guest.InputBlob}
    {caller target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (returned : StateInitReturned input caller target pointer si boundary) :
    target.globals.lookup (ofString "frame_mem_ptr")=caller.globals.lookup (ofString "frame_mem_ptr") :=
  returned.globals _ (by decide)

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.hash_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.frame_cursor
