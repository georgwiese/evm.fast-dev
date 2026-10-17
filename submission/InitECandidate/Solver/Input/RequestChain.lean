import InitECandidate.Solver.Input.RequestLoad

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem chain_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : 18≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat) (cursorRoom : cursor.toNat+96≤33806089496) :
    evaluateHOLFiniteState (allocated source cursor witness) chainStore=(none,chained source input cursor witness) ∧
      Blob.HeapInput (chained source input cursor witness) input pointer := by
  classical
  have loadedP:=(loaded_locals source pointer witness pointerLocal).1
  have p : (allocated source cursor witness).locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))) := by
    exact (bind_lookup_other (WitnessRadix.PersistentAlloc.post {loaded source witness with clock:=source.clock-1} cursor 96#64)
      "si" "p" cursor (by decide)).trans loadedP
  have si : (allocated source cursor witness).locals.lookup (ofString "si")=some (.val (.word cursor)) := bind_lookup_same _ _ _
  have pRead : eval (allocated source cursor witness) (localVar "p")=some (.val (.word (pointer+2#64))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using p
  have siRead : eval (allocated source cursor witness) (localVar "si")=some (.val (.word cursor)) := by
    simpa [eval,localVar,evalHOLExact,toExact] using si
  have allocatedHeap : Blob.HeapInput (allocated source cursor witness) input pointer :=
    Blob.HeapInput.of_fields source _ input pointer rfl rfl rfl heap
  have number : (cursor+88#64).toNat=cursor.toNat+88 := by
    rw [BitVec.toNat_add_of_lt (by change cursor.toNat+88<2^64; omega)]
    rfl
  have mapped : (allocated source cursor witness).memaddrs (cursor+88#64) := by
    change source.memaddrs (cursor+88#64)
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [number]; omega
    · rw [number]; omega
    · rw [number]; omega
  have result:=Scalar.store_le64 (allocated source cursor witness) input pointer (pointer+2#64) (cursor+88#64)
    (localVar "p") (Scalar.plus (localVar "si") 88) [8] 10 allocatedHeap inside pRead
    (by simp [BitVec.add_assoc]) (Scalar.plus_read _ _ cursor 88 siRead) mapped pointerAligned (by omega)
    (Or.inr (by rw [number]; omega))
  exact result

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.chain_execute
