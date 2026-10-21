import InitECandidate.Solver.Input.ByteWriterMemory
import InitECandidate.Solver.GasBudget.Be64Normal
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem be64_call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (pointer value query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word pointer),.val (.word value)])
    (arena : AllocatedBytes.Arena pointer 8) (away : CopyGeneral.Away pointer query 8)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be64") arguments)=(none,post)) : post.memory query=source.memory query := by
  have code := GasBudget.MemoryWriter.be64_code source.code installed
  obtain ⟨callee,called,pLocal,vLocal⟩ := environment source.code.lookup (ofString "st_be64") GasBudget.MemoryWriter.Kind.be64.body pointer value code
  apply MemoryAt.call_normal source post (ofString "st_be64") arguments [.val (.word pointer),.val (.word value)] GasBudget.MemoryWriter.Kind.be64.body callee .one query args called _ run
  intro target returned evaluated
  have mapped : GasBudget.MemoryWriter.BytesMapped (callEntryStateHOLFinite source callee) pointer 8 := by
    intro offset inside
    exact AllocatedBytes.byte_mapped (callEntryStateHOLFinite source callee) pointer 8 offset domain arena inside
  obtain ⟨zero,paid,paidBound,funded,clock,frame,memory⟩ := GasBudget.MemoryWriter.be64_normal (callEntryStateHOLFinite source callee) target pointer value installed pLocal vLocal mapped returned evaluated
  exact memory query (by intro offset inside; exact (away offset inside).2)

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be64_call_memory
