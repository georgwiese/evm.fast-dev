import InitECandidate.Solver.Input.Requests.AllocatedBody

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

structure Layout (words : Nat → BitVec 64) (total : BitVec 64) : Prop where
  first : words 0 = 20#64
  valid : ∀ index < 5,Offsets.ValidAt 20#64 total words index

/-- Entire original request body after its minimum-length guard, including
all offset/list rejections. The bound348 is a source call/loop bound, and the
normal return exposes the real request image, validated input layout, exact
heap update and every protected ordinary word/full FFI/control field. -/
theorem after_guard_body (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob array cursor total : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input blob) (extent : start + 20 ≤ input.length % 2^64)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (blob + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word total)))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (installed : OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (domain : source.memaddrs = InitE.ordinaryDomain) (blobAligned : blob.toNat % 8 = 0)
    (arrayAligned : array.toNat % 8 = 0) (arrayLower : 2701131776 ≤ array.toNat)
    (arrayBefore : array.toNat + 40 ≤ blob.toNat) (upper : blob.toNat + input.length % 2^64 + 8 ≤ 33806089496)
    (arena : Arena cursor 80) (cursorAligned : cursor.toNat % 8 = 0)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)))
    (afterInput : blob.toNat + input.length % 2^64 + 8 ≤ cursor.toNat)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64 ∨ error = 30#64 ∨ error = 31#64) ∧
      result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 348) ∨
    (result = some (.returned (.val (.word cursor))) ∧ Blob.HeapInput post input blob ∧ source.clock - post.clock ≤ 348 ∧ post.clock ≤ source.clock ∧
      BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) ∧
      (∀ query,(query.toNat < array.toNat ∨ array.toNat + 40 ≤ query.toNat) → (query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat) → post.memory query = source.memory query) ∧
      Layout (offsetWord input start) total ∧ ∃ counts : Nat → BitVec 64,Image post (blob + BitVec.ofNat 64 start) cursor total (offsetWord input start) counts) := by
  rcases offsets_trace source post input blob array total start heap extent p n offsets domain blobAligned arrayAligned arrayLower arrayBefore upper
    (Main.DecoderCall.original_offsets_code source.code installed) (Main.DecoderCall.original_fail_code source.code installed) shape result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    refine Or.inl ⟨error,?_,same,by omega⟩
    rcases allowed with rfl | rfl | rfl <;> simp
  · obtain ⟨first,valid,next,innerPost,forward,cost,control,bytes,other,cells,remaining,restored,offsetMemory⟩ := normal
    have globals : next.globals = source.globals := by have h := congrArg PanSemStateFiniteExact.globals control; exact h
    have codes : next.code = source.code := by have h := congrArg PanSemStateFiniteExact.code control; exact h
    have shapes : next.eshapes = source.eshapes := by have h := congrArg PanSemStateFiniteExact.eshapes control; exact h
    have addresses : next.memaddrs = source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs control; exact h
    have nextOffsets : next.globals.lookup (ofString "ssz_offs") = some (.val (.word array)) := by rw [globals]; exact offsets
    have nextHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)) := by rw [globals]; exact heapGlobal
    have nextShape : next.eshapes.lookup (ofString "SszErr") = some .one := by rw [shapes]; exact shape
    rcases allocated_body next innerPost input blob array (blob + BitVec.ofNat 64 start) cursor total start bytes
      ((other _ (by decide)).trans p) ((other _ (by decide)).trans n) nextOffsets cells (codes.symm ▸ installed) nextShape
      (addresses.trans domain) arrayAligned ⟨arrayLower,by omega⟩ arena nextHeap blobAligned cursorAligned afterInput result remaining notTimeout with rejected | normal
    · obtain ⟨error,allowed,same,tailCost⟩ := rejected
      have finalClock : post.clock = innerPost.clock := by rw [restored]; rfl
      have innerForward := evaluateHOLFiniteState_clock_le next afterOffsets
      rw [remaining] at innerForward
      change innerPost.clock ≤ next.clock at innerForward
      refine Or.inl ⟨error,?_,same,by rw [finalClock]; omega⟩
      rcases allowed with rfl | rfl <;> simp
    · obtain ⟨same,innerBytes,tailCost,innerForward,innerControl,innerOutside,counts,image⟩ := normal
      have finalFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite innerPost := by rw [restored]; rfl
      have memory : post.memory = innerPost.memory := by have h := congrArg PanSemStateFiniteExact.memory finalFrame; exact h
      have finalDomain : post.memaddrs = innerPost.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs finalFrame; exact h
      have finalEndian : post.be = innerPost.be := by have h := congrArg PanSemStateFiniteExact.be finalFrame; exact h
      have finalClock : post.clock = innerPost.clock := by have h := congrArg PanSemStateFiniteExact.clock finalFrame; exact h
      have finalBytes := Blob.HeapInput.of_fields innerPost post input blob memory.symm finalDomain.symm finalEndian.symm innerBytes
      have updatedControl : BackingLayout.control (PersistentAlloc.post next cursor 80#64) = BackingLayout.control (PersistentAlloc.post source cursor 80#64) := by
        have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => BackingLayout.control (PersistentAlloc.post state cursor 80#64)) control
        exact h
      have finalControl : BackingLayout.control post = BackingLayout.control (PersistentAlloc.post source cursor 80#64) := by
        have h := congrArg BackingLayout.control finalFrame
        exact h.trans (innerControl.trans updatedControl)
      have outside (query : BitVec 64) (notOffsets : query.toNat < array.toNat ∨ array.toNat + 40 ≤ query.toNat)
          (notRequest : query.toNat < cursor.toNat ∨ cursor.toNat + 80 ≤ query.toNat) : post.memory query = source.memory query := by
        rw [memory]
        exact (innerOutside query notRequest).trans (offsetMemory query notOffsets)
      have finalImage : Image post (blob + BitVec.ofNat 64 start) cursor total (offsetWord input start) counts :=
        ⟨by intro index small; rw [memory]; exact image.cells index small,image.arithmetic⟩
      exact Or.inr ⟨same,finalBytes,by rw [finalClock]; omega,by rw [finalClock]; omega,finalControl,outside,⟨first,valid⟩,counts,finalImage⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.after_guard_body
