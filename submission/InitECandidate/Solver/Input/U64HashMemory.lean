import InitECandidate.Solver.Input.U64HashCallCost
import InitECandidate.Solver.Input.MemoryContinue
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.U64Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_zero_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) (away : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (.return (.const 0#64)) value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) copyArguments=some (CopyGeneral.values out p 8) := by
    simp [copyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,pointer,output,CopyGeneral.values]
  have front := MemoryAt.copy_normal source middle copyArguments p out query 8 args installed domain inputArena (AllocatedBytes.Arena.weaken out 32 8 outArena (by decide))
    (by simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange out query 32 0 8 away (by decide)) normal
  have finalFrame := MemoryAt.return_current middle (.const 0#64) query
  rw [remaining] at finalFrame
  exact finalFrame.trans front

/-- Actual original scalar hashing only changes its real output32. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p))) (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (away : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ afterZero value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values out 32) := by
    simp [zeroArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,output,Zero.values]
  have front := MemoryAt.zero_normal source middle zeroArguments out query 32 args installed domain outArena aligned (by decide) (by intro offset inside; exact (away offset inside).1) normal
  have other (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "memzero") zeroArguments normal
  have fields := evaluation_fields source middle _ none normal
  have tail := after_zero_memory middle post p out query (fields.2.2.2.symm ▸ installed) (fields.1.trans domain) ((other "p").trans pointer) ((other "out").trans output) inputArena outArena away value remaining
  exact tail.trans front

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (inputArena : AllocatedBytes.Arena p 8) (outArena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (away : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_u64_at") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,outLocal⟩ := environment source.code.lookup p out (original_code source.code installed)
  exact MemoryAt.call_normal source post (ofString "htr_u64_at") arguments (values p out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p out query installed domain pLocal outLocal inputArena outArena aligned away value evaluated) run

end InitECandidate.Solver.Input.U64Hash

#print axioms InitECandidate.Solver.Input.U64Hash.after_zero_memory
#print axioms InitECandidate.Solver.Input.U64Hash.body_memory
#print axioms InitECandidate.Solver.Input.U64Hash.call_memory
