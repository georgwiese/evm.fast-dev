import InitECandidate.Solver.Input.RequestPrefixNormal

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure ReadyFrame (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) : Prop where
  code : ready.code=source.code
  exceptions : ready.eshapes=source.eshapes
  structs : ready.structs=source.structs
  domain : ready.memaddrs=source.memaddrs
  shared : ready.shMemaddrs=source.shMemaddrs
  endian : ready.be=source.be
  ffi : ready.ffi=source.ffi
  globals : ready.globals=source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 96#64)))
  clockLower : source.clock-5≤ready.clock

/-- Normal execution of the full fixed decoder reaches the actual request
body at blob+18 with a safe >=44-byte slice and copied-byte correspondence.
Schema, both first-container offsets and the request extent derive from execution. -/
theorem from_header (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array cursor : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (cursorAligned : cursor.toNat%8=0) (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+96≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 6≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source Header.body=(some (.returned value),post)) :
    Guest.GasLimit.le32 input 2=16 ∧ 62≤input.length%2^64 ∧
      ∃ ready innerPost,ReadyFrame source ready cursor ∧ Blob.HeapInput ready input pointer ∧
        ready.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))) ∧
        ready.locals.lookup (ofString "nlen")=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6-16)))) ∧
        44≤Guest.GasLimit.le32 input 6-16 ∧ Guest.GasLimit.le32 input 6-16≤input.length%2^64-18 ∧
        evaluateHOLFiniteState ready requestBody=(some (.returned value),innerPost) := by
  classical
  obtain ⟨extent,schema0,schema1,first,witnessLower,witnessUpper,next,paid,bound,nextEq,nextHeap,nextRun⟩:=
    Header.first_container source post input pointer array heap pointerLocal lengthLocal arrayGlobal domain pointerAligned arrayAligned upper
      arrayLower (by omega) code failCode exceptionShape (by omega) value run
  have number : (array+8#64).toNat=array.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change array.toNat+8<2^64; omega)]
    rfl
  have different : array+8#64≠array := by
    intro equal
    have h:=congrArg BitVec.toNat equal
    rw [number] at h
    omega
  have firstMapped : next.memaddrs array := by
    rw [nextEq]
    change source.memaddrs array
    rw [domain]
    exact WitnessRadix.BackingLayout.ordinary_mapped array arrayLower (by omega) arrayAligned
  have secondMapped : next.memaddrs (array+8#64) := by
    rw [nextEq]
    change source.memaddrs (array+8#64)
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [number]; omega
    · rw [number]; omega
    · rw [number]; omega
  have firstCell : next.memory array=.word 16#64 := by
    rw [nextEq]
    simp [Header.pairState,Header.firstState,Header.firstWord,WitnessRadix.StoreWord.put,Ne.symm different,first]
  have secondCell : next.memory (array+8#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6)) := by
    rw [nextEq]
    simp [Header.pairState,Header.secondWord,WitnessRadix.StoreWord.put]
  have p : next.locals.lookup (ofString "p")=some (.val (.word (pointer+2#64))) := by
    rw [nextEq]
    change (Header.shifted source pointer (input.length%2^64)).locals.lookup (ofString "p")=_
    exact (bind_lookup_other (WitnessRadix.QueryBranch.bind source "p" (pointer+2#64)) "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  have globals : next.globals=source.globals := by rw [nextEq]; rfl
  have nextDomain : next.memaddrs=InitE.ordinaryDomain := by rw [nextEq]; exact domain
  have nextCode : next.code=source.code := by rw [nextEq]; rfl
  have nextShapes : next.eshapes=source.eshapes := by rw [nextEq]; rfl
  have nextClock : next.clock=source.clock-paid := by rw [nextEq]
  obtain ⟨restoreStack,setupRun,readyHeap⟩:=setup next input pointer array cursor (Guest.GasLimit.le32 input 6) witnessLower nextHeap extent p
    (by rw [globals]; exact arrayGlobal) firstMapped secondMapped firstCell secondCell nextDomain pointerAligned cursorAligned (by omega)
    cursorAfter cursorRoom (by rw [globals]; exact heapGlobal) (by rw [nextCode]; exact allocCode) (by rw [nextClock]; omega)
  obtain ⟨safeExtent,safeLength,safeUpper,np,nlen,innerPost,requestRun⟩:=normal_prefix next post input pointer cursor (Guest.GasLimit.le32 input 6)
    witnessUpper restoreStack setupRun (by rw [nextCode]; exact failCode) (by rw [nextShapes]; exact exceptionShape) (by rw [nextClock]; omega) value nextRun
  let ready:=prepared next input pointer cursor (Guest.GasLimit.le32 input 6)
  have metadata : ReadyFrame source ready cursor := by
    constructor
    · change next.code=source.code
      exact nextCode
    · change next.eshapes=source.eshapes
      exact nextShapes
    · change next.structs=source.structs
      rw [nextEq]
      rfl
    · change next.memaddrs=source.memaddrs
      rw [nextEq]
      rfl
    · change next.shMemaddrs=source.shMemaddrs
      rw [nextEq]
      rfl
    · change next.be=source.be
      rw [nextEq]
      rfl
    · change next.ffi=source.ffi
      rw [nextEq]
      rfl
    · change next.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 96#64)))=_
      rw [globals]
    · change source.clock-5≤next.clock-1
      rw [nextClock]
      omega
  exact ⟨first,safeExtent,ready,innerPost,metadata,readyHeap,np,nlen,safeLength,safeUpper,requestRun⟩

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.from_header
