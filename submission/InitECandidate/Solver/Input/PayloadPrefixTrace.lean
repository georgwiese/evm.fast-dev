import InitECandidate.Solver.Input.PayloadPrefixSetup
import InitECandidate.Solver.Input.TerminatingProgramPrefix

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open WitnessRadix.ProgramPrefix

/-- The actual enclosing payload execution supplies its real allocation
clock and reaches the original four-offset body. Both header stores, every
raw offset declaration, all bytes and lexical restorations are retained. -/
theorem prefix_setup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ ∃ innerPost,
      Executes source prefixActions (prepared source input pointer cursor length) (restorePrefix source input pointer cursor length) ∧
      Blob.HeapInput (prepared source input pointer cursor length) input pointer ∧
      evaluateHOLFiniteState (prepared source input pointer cursor length) offsetBody = (result,innerPost) ∧ post = restorePrefix source input pointer cursor length innerPost := by
  obtain ⟨padded,_⟩ := prefix_setup {source with clock := source.clock + 1} input pointer cursor length heap inside p n domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode (by simp)
  rw [prefix_shape] at run
  have paid := terminating_program_prefix source post (prepared {source with clock := source.clock + 1} input pointer cursor length) prefixActions offsetBody (restorePrefix {source with clock := source.clock + 1} input pointer cursor length) 1 padded result run notTimeout
  have funded : 1 ≤ source.clock := by change 1 ≤ source.clock + 1 - 1 at paid; omega
  obtain ⟨setup,bytes⟩ := prefix_setup source input pointer cursor length heap inside p n domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode funded
  rw [WitnessRadix.ProgramPrefix.execute setup offsetBody] at run
  let innerPost := (evaluateHOLFiniteState (prepared source input pointer cursor length) offsetBody).2
  have observed := congrArg Prod.fst run
  exact ⟨funded,innerPost,setup,bytes,Prod.ext observed rfl,(congrArg Prod.snd run).symm⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prefix_setup_trace
