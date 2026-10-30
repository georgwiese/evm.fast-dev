import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.CurrentKeccak.OutputMemory
import InitECandidate.Solver.Input.ByteStoreFrame

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- A reached normal phase retains its actual workspace, caller locals and
one protected memory word. It assumes no later phase completion. -/
structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad query : BitVec 64) : Prop where
  environment : Environment target stp pad
  memory : target.memory query=source.memory query
  locals : ∀ key,target.locals.lookup key=source.locals.lookup key

theorem Frame.cell {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pad query : BitVec 64}
    (frame : Frame source target stp pad query) (key : MlS) (value : ValueHOL 64)
    (cell : source.locals.lookup key=some value) : target.locals.lookup key=some value := (frame.locals key).trans cell

theorem zero_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (arena : AllocatedBytes.Arena dst length) (aligned : dst.toNat%8=0) (multiple : length%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>zero_call_globals key source.code environment.installed arguments) run,
   MemoryAt.zero_normal source post arguments dst query length args environment.installed environment.domain arena aligned multiple away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "memzero") arguments run⟩

/-- Actual normal copy writes are confined to the known destination span.
No input or output arena is needed to derive this successful-run frame. -/
theorem copy_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad src dst query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (small : length+32<2^64) (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) : Frame source post stp pad query := by
  have span:=CopyAny.call_span_normal source post dst src length small arguments args environment.installed run
  exact ⟨environment.after _ _ (fun key=>copy_call_globals key source.code environment.installed arguments) run,
    span.1.memory query away,fun key=>CallNormal.ignored_lookup source post key (ofString "memcpy") arguments run⟩

theorem absorb_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad blk query : BitVec 64)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Absorb.values stp blk))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_absorb_block") arguments)=(none,post)) : Frame source post stp pad query :=
  ⟨environment.after _ _ (fun key=>absorb_call_globals key source.code environment.installed arguments) run,
   Absorb.call_memory source post stp blk query environment.installed arguments args away run,
   fun key=>CallNormal.ignored_lookup source post key (ofString "keccak_absorb_block") arguments run⟩

theorem byte_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad address query : BitVec 64)
    (environment : Environment source stp pad) (destination expression : ExpHOL 64)
    (read : eval source destination=some (.val (.word address))) (away : query≠panByteAlignHOL (width:=64) address)
    (run : evaluateHOLFiniteState source (.storeByte destination expression)=(none,post)) : Frame source post stp pad query := by
  have frame:=Input.byte_store_normal_frame source post destination expression address read run
  exact ⟨environment.after _ _ (fun key=>GlobalEffects.byte_store key source.code destination expression) run,
    frame.2 query away,by intro key; rw [frame.1]⟩

theorem output_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code outProgram := by
  apply GlobalEffects.conditional
  · unfold outWords outStore
    repeat first | apply GlobalEffects.sequence | exact GlobalEffects.store key code _ _
  · exact copy_call_globals key code installed _

theorem output_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad out query : BitVec 64)
    (environment : Environment source stp pad)
    (stateCell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (outArena : AllocatedBytes.Arena out 32) (away : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source outProgram=(none,post)) : Frame source post stp pad query := by
  refine ⟨environment.after _ _ (fun key=>output_globals key source.code environment.installed) run,
    output_memory source post stp pad out query environment stateCell outCell outArena away run,?_⟩
  intro key
  have safe : LocalPrefix key outProgram := .ite _
    (.seq (.store _ _) (.seq (.store _ _) (.seq (.store _ _) (.store _ _))))
    (.call none _ _ (by intro name impossible; cases impossible))
  have kept:=(safe.summary_full source).1
  rw [run] at kept
  exact kept rfl

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.zero_frame
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.copy_frame
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.absorb_frame
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.byte_frame
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.output_frame
