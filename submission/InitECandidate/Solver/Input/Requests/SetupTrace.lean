import InitECandidate.Solver.Input.Requests.Setup
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

/-- An actual non-timeout request continuation funds its one real allocator
tick and reaches all five fixed-list calls with the five validated offsets.
The subsequent list results remain arbitrary. -/
theorem setup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array cursor : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (cells : ∀ position < 5,source.memory (byteAddress array (8*position)) = .word (offsetWord input start position))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arrayAligned : array.toNat % 8 = 0) (arrayArena : Arena array 40)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (room : cursor.toNat + 80 ≤ 33806089496)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterOffsets = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ ∃ innerPost,
      Executes source setupActions (prepared source input cursor start) (restoreSetup source input cursor start) ∧
      Blob.HeapInput (prepared source input cursor start) input pointer ∧
      evaluateHOLFiniteState (prepared source input cursor start) countCalls = (result,innerPost) ∧ post = restoreSetup source input cursor start innerPost := by
  obtain ⟨padded,_⟩ := setup {source with clock := source.clock + 1} input pointer array cursor start heap offsets cells domain arrayAligned arrayArena heapGlobal allocCode room (by simp)
  rw [setup_shape] at run
  have paid := terminating_program_prefix source post (prepared {source with clock := source.clock + 1} input cursor start) setupActions countCalls (restoreSetup {source with clock := source.clock + 1} input cursor start) 1 padded result run notTimeout
  have funded : 1 ≤ source.clock := by change 1 ≤ source.clock + 1 - 1 at paid; omega
  obtain ⟨actual,bytes⟩ := setup source input pointer array cursor start heap offsets cells domain arrayAligned arrayArena heapGlobal allocCode room funded
  rw [WitnessRadix.ProgramPrefix.execute actual countCalls] at run
  let innerPost := (evaluateHOLFiniteState (prepared source input cursor start) countCalls).2
  have observed := congrArg Prod.fst run
  exact ⟨funded,innerPost,actual,bytes,Prod.ext observed rfl,(congrArg Prod.snd run).symm⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.setup_trace
