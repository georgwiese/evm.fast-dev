import InitECandidate.Solver.Rlp.DecodeCallFrame
import InitECandidate.Solver.Rlp.DecodeGlobals
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Facts obtained only from an actual checked return of the original full
RLP decoder, relative to the same caller and physical scratch arena. -/
structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit : BitVec 64) (answer : ValueHOL 64) : Prop where
  complete : Complete pointer length answer
  arena : Validation.Arena target cursor limit
  memory : Validation.Above source target cursor.toNat
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  globals : ∀ key,target.globals.lookup key=source.globals.lookup key
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤60*length.toNat+44

/-- All enclosing outcomes are covered: either the scoped call stops within
its own allowance or its real continuation receives a complete decoded item
and the derived physical memory/global frame. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_decode_fully") expressions continuation)=(result,post)) :
    source.clock-post.clock≤60*length.toNat+44 ∨
      ∃ target answer inner,Returned source target pointer length cursor limit answer ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(result,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") body Item.resultShape pointer length (original_code source.code installed)
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have price := body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  rcases Input.CallNormal.scoped_trace source post name Item.resultShape (ofString "rlp_decode_fully") expressions _ body continuation callee Item.resultShape (60*length.toNat+43)
      args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨complete,nextArena,above,_⟩ := body_normal_above (callEntryStateHOLFinite source callee) target pointer length cursor limit pointerLocal lengthLocal entryArena fits installed answer bodyRun
    have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned answer)) bodyRun
    have globalsFrame (key : MlS) : target.globals.lookup key=source.globals.lookup key := by
      by_cases scratch : key=ofString "scratch_ptr"
      · rw [scratch,nextArena.cursorGlobal,arena.cursorGlobal]
      · have pure := globals key source.code installed scratch (callEntryStateHOLFinite source callee) rfl
        rw [bodyRun] at pure
        exact congrArg Prod.snd pure
    exact Or.inr ⟨target,answer,inner,⟨complete,nextArena,above,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,globalsFrame,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.scoped_trace
