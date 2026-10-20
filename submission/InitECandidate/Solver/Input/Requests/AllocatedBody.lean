import InitECandidate.Solver.Input.Requests.CountsBody
import InitECandidate.Solver.Input.Requests.PreparedLocals
import InitECandidate.Solver.Input.Requests.SetupReached

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical original request arrays and their actual element counts. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor total : BitVec 64) (words counts : Nat → BitVec 64) : Prop where
  cells : ∀ index < 5,source.memory (cursor + BitVec.ofNat 64 (16*index)) = .word (pointer + words index) ∧
    source.memory (cursor + BitVec.ofNat 64 (16*index+8)) = .word (counts index)
  arithmetic : ∀ index < 5,(counts index).toNat = (countSpan words total index).toNat / (elementSize index).toNat ∧
    (countSpan words total index).toNat % (elementSize index).toNat = 0


private theorem normal_frontier (source post ready innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob pointer cursor total : BitVec 64) (start : Nat)
    (funded : 1 ≤ source.clock) (readyClock : ready.clock = source.clock - 1)
    (readyControl : BackingLayout.control ready = BackingLayout.control (PersistentAlloc.post source cursor 80#64))
    (readyMemory : ready.memory = source.memory)
    (finalFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite innerPost)
    (postBytes : Blob.HeapInput innerPost input blob) (cost : ready.clock - innerPost.clock ≤ 335) (forward : innerPost.clock ≤ ready.clock)
    (control : BackingLayout.control innerPost = BackingLayout.control ready)
    (outside : ∀ query,query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat → innerPost.memory query = ready.memory query)
    (counts : Nat → BitVec 64) (originalImage : Image innerPost pointer cursor total (offsetWord input start) counts) :
    Blob.HeapInput post input blob ∧ source.clock - post.clock ≤ 336 ∧ post.clock ≤ source.clock ∧
      BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) ∧
      (∀ query,query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat → post.memory query = source.memory query) ∧
      ∃ counts : Nat → BitVec 64,Image post pointer cursor total (offsetWord input start) counts := by
  have memory : post.memory = innerPost.memory := by have h := congrArg PanSemStateFiniteExact.memory finalFrame; exact h
  have addresses : post.memaddrs = innerPost.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs finalFrame; exact h
  have endian : post.be = innerPost.be := by have h := congrArg PanSemStateFiniteExact.be finalFrame; exact h
  have clock : post.clock = innerPost.clock := by have h := congrArg PanSemStateFiniteExact.clock finalFrame; exact h
  have finalBytes := Blob.HeapInput.of_fields innerPost post input blob memory.symm addresses.symm endian.symm postBytes
  have finalControl : BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) := by
    have projected := congrArg BackingLayout.control finalFrame
    exact projected.trans (control.trans readyControl)
  have finalOutside (query : BitVec 64) (away : query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat) : post.memory query = source.memory query := by
    rw [memory]
    exact (outside query away).trans (congrFun readyMemory query)
  have image : Image post pointer cursor total (offsetWord input start) counts := ⟨by intro index small; rw [memory]; exact originalImage.cells index small,originalImage.arithmetic⟩
  exact ⟨finalBytes,by rw [clock]; omega,by rw [clock]; omega,finalControl,finalOutside,counts,image⟩

private theorem compose_counts (source post ready innerPost : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob pointer cursor total : BitVec 64) (start : Nat) (funded : 1 ≤ source.clock) (readyClock : ready.clock = source.clock - 1)
    (readyControl : BackingLayout.control ready = BackingLayout.control (PersistentAlloc.post source cursor 80#64)) (readyMemory : ready.memory = source.memory)
    (finalFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite innerPost)
    (model : CountLocals ready (offsetWord input start) total pointer cursor)
    (installed : OriginalCode.Installed ready.code) (shape : ready.eshapes.lookup (ofString "SszErr") = some .one)
    (bytes : Blob.HeapInput ready input blob) (domain : ready.memaddrs = InitE.ordinaryDomain) (arena : Arena cursor 80)
    (blobAligned : blob.toNat % 8 = 0) (cursorAligned : cursor.toNat % 8 = 0) (afterInput : blob.toNat + input.length % 2^64 + 8 ≤ cursor.toNat)
    (result : Option (PanSemResultExact 64)) (remaining : evaluateHOLFiniteState ready countCalls = (result,innerPost)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 336) ∨
    (result = some (.returned (.val (.word cursor))) ∧ Blob.HeapInput post input blob ∧ source.clock - post.clock ≤ 336 ∧ post.clock ≤ source.clock ∧
      BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) ∧
      (∀ query,query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat → post.memory query = source.memory query) ∧
      ∃ counts : Nat → BitVec 64,Image post pointer cursor total (offsetWord input start) counts) := by
  rcases counts_body ready innerPost input blob pointer cursor total (offsetWord input start) model installed shape
    bytes domain arena blobAligned cursorAligned afterInput result remaining notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have postClock : post.clock = innerPost.clock := by have h := congrArg PanSemStateFiniteExact.clock finalFrame; exact h
    have forward := evaluateHOLFiniteState_clock_le ready countCalls
    rw [remaining] at forward
    change innerPost.clock ≤ ready.clock at forward
    exact Or.inl ⟨error,allowed,same,by rw [postClock]; omega⟩
  · obtain ⟨same,postBytes,cost,forward,control,outside,counts,imageCells,arithmetic⟩ := normal
    have originalImage : Image innerPost pointer cursor total (offsetWord input start) counts := ⟨imageCells,arithmetic⟩
    exact Or.inr ⟨same,normal_frontier source post ready innerPost input blob pointer cursor total start funded readyClock readyControl readyMemory finalFrame
      postBytes cost forward control outside counts originalImage⟩

/-- Complete original request allocation/load/list/store suffix at its actual
clock. Parser rejection or a real request return costs at most336ticks; the
normal result retains the exact80-byte image, heap advance, input bytes and
full FFI/control frame. -/
theorem allocated_body (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (blob array pointer cursor total : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input blob)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n : source.locals.lookup (ofString "len") = some (.val (.word total)))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (cells : ∀ position < 5,source.memory (byteAddress array (8*position)) = .word (offsetWord input start position))
    (installed : OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arrayAligned : array.toNat % 8 = 0) (arrayArena : Arena array 40) (arena : Arena cursor 80)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)))
    (blobAligned : blob.toNat % 8 = 0) (cursorAligned : cursor.toNat % 8 = 0)
    (afterInput : blob.toNat + input.length % 2^64 + 8 ≤ cursor.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterOffsets = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 30#64 ∨ error = 31#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 336) ∨
    (result = some (.returned (.val (.word cursor))) ∧ Blob.HeapInput post input blob ∧ source.clock - post.clock ≤ 336 ∧ post.clock ≤ source.clock ∧
      BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) ∧
      (∀ query,query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat → post.memory query = source.memory query) ∧
      ∃ counts : Nat → BitVec 64,Image post pointer cursor total (offsetWord input start) counts) := by
  obtain ⟨funded,innerPost,bytes,remaining,finalFrame⟩ := setup_reached source post input blob array cursor start heap offsets cells domain arrayAligned arrayArena heapGlobal
    (PersistentAlloc.original_code source.code installed) arena.upper result run notTimeout
  let ready := prepared source input cursor start
  have model := prepared_model source input cursor pointer total start p n
  exact compose_counts source post ready innerPost input blob pointer cursor total start funded (prepared_clock source input cursor start)
    (prepared_control source input cursor start) (prepared_memory source input cursor start) finalFrame model
    installed shape bytes domain arena blobAligned cursorAligned afterInput result remaining notTimeout

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.allocated_body
