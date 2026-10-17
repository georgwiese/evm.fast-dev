import InitECandidate.Solver.Input.RequestPositions

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- All literal declarations, real allocation and chain-id store before the
request-length guard, with complete lexical-restoration evidence. -/
theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : 1≤source.clock) :
    ∃ restoreStack,Executes source actions (prepared source input pointer cursor witness) restoreStack ∧
      Blob.HeapInput (prepared source input pointer cursor witness) input pointer := by
  have firstRead:=first_read source array arrayGlobal firstMapped firstCell
  have secondRead:=second_read source array witness arrayGlobal secondMapped secondCell
  obtain ⟨chainRun,chainHeap⟩:=chain_execute source input pointer cursor witness heap inside pointerLocal domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom
  have npRead:=pointer_read source input pointer cursor witness pointerLocal
  have nlenRead:=length_read source input pointer cursor witness witnessLower pointerLocal
  refine ⟨restorePrefix source input pointer cursor witness,?_,?_⟩
  · exact .declare 16#64 firstRead
      (.declare (BitVec.ofNat 64 witness) secondRead
        (.allocate cursor 96#64 rfl allocCode heapGlobal
          (by change cursor.toNat+96≤33806089496; exact cursorRoom) enough
          (.command chainRun (Nat.le_refl _)
            (.declare (pointer+18#64) npRead (.declare (BitVec.ofNat 64 (witness-16)) nlenRead (.done _))))))
  · exact Blob.HeapInput.of_fields (chained source input cursor witness) (prepared source input pointer cursor witness) input pointer rfl rfl rfl chainHeap

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.setup
