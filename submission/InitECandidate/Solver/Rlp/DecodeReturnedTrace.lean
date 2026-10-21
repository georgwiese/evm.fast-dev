import InitECandidate.Solver.Rlp.DecodeTrace
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine successful scoped return supplies the full current parser contract. -/
theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_decode_fully") expressions continuation)=(some (.returned value),post)) :
    ∃ target answer inner,Returned source target pointer length cursor limit answer ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") body Item.resultShape pointer length (original_code source.code installed)
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price := body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩ :=
    Input.CallNormal.scoped_normal source post name Item.resultShape (ofString "rlp_decode_fully") expressions _ body continuation callee Item.resultShape args called value run
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock price
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤60*length.toNat+43 at price
  have forward : target.clock≤source.clock := by omega
  have cost : source.clock-target.clock≤60*length.toNat+44 := by omega
  obtain ⟨complete,nextArena,above,_⟩ := body_normal_above (callEntryStateHOLFinite source callee) target pointer length cursor limit pointerLocal lengthLocal entryArena fits installed answer bodyRun
  have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned answer)) bodyRun
  have globalsFrame (key : MlS) : target.globals.lookup key=source.globals.lookup key := by
    by_cases scratch : key=ofString "scratch_ptr"
    · rw [scratch,nextArena.cursorGlobal,arena.cursorGlobal]
    · have pure := globals key source.code installed scratch (callEntryStateHOLFinite source callee) rfl
      rw [bodyRun] at pure
      exact congrArg Prod.snd pure
  exact ⟨target,answer,inner,⟨complete,nextArena,above,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,globalsFrame,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.scoped_returned
