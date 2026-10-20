import InitECandidate.Solver.Input.RequestSetup
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- The actual enclosing run funds the real SI96 allocation and reaches the
original request-length guard with all copied bytes and lexical restorations.
Neither a successful request nor a future helper result is a premise. -/
theorem setup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array cursor : BitVec 64) (witness : Nat) (witnessLower : 16≤witness)
    (heap : Blob.HeapInput source input pointer) (inside : 18≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (firstMapped : source.memaddrs array) (secondMapped : source.memaddrs (array+8#64))
    (firstCell : source.memory array=.word 16#64) (secondCell : source.memory (array+8#64)=.word (BitVec.ofNat 64 witness))
    (domain : source.memaddrs=InitE.ordinaryDomain) (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat) (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+96≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))

    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source prefixBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ ∃ restoreStack innerPost,
      Executes source actions (prepared source input pointer cursor witness) restoreStack ∧
      Blob.HeapInput (prepared source input pointer cursor witness) input pointer ∧
      evaluateHOLFiniteState (prepared source input pointer cursor witness) (.seq lengthGuard requestBody) = (result,innerPost) ∧ post = restoreStack innerPost := by
  obtain ⟨paddedRestore,padded,_⟩ := setup {source with clock := source.clock + 1} input pointer array cursor witness witnessLower heap inside pointerLocal arrayGlobal firstMapped secondMapped firstCell secondCell domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode (by simp)
  rw [actions_shape] at run
  have paid := terminating_program_prefix source post (prepared {source with clock := source.clock + 1} input pointer cursor witness) actions (.seq lengthGuard requestBody) paddedRestore 1 padded result run notTimeout
  have funded : 1 ≤ source.clock := by change 1 ≤ source.clock + 1 - 1 at paid; omega
  obtain ⟨restoreStack,actual,bytes⟩ := setup source input pointer array cursor witness witnessLower heap inside pointerLocal arrayGlobal firstMapped secondMapped firstCell secondCell domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode funded
  rw [WitnessRadix.ProgramPrefix.execute actual (.seq lengthGuard requestBody)] at run
  let innerPost := (evaluateHOLFiniteState (prepared source input pointer cursor witness) (.seq lengthGuard requestBody)).2
  have actualResult : (evaluateHOLFiniteState (prepared source input pointer cursor witness) (.seq lengthGuard requestBody)).1 = result := congrArg Prod.fst run
  exact ⟨funded,restoreStack,innerPost,actual,bytes,Prod.ext actualResult rfl,(congrArg Prod.snd run).symm⟩

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.setup_trace
