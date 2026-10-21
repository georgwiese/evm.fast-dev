import InitECandidate.Solver.Input.MainRequestRootHashLayout

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.Main.RequestRootHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual heap global selects the same prehash frontier already
proved for normal main decoding; no independent hypothetical heap is used. -/
theorem frontier (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word root))) :
    root.toNat%8=0 ∧ (DecoderCall.witnessArray input).toNat≤root.toNat ∧
      root.toNat≤DecoderSetup.cursor input+600+4*(input.length%2^64) ∧ AllocatedBytes.Arena root 32 := by
  obtain ⟨pointer,stored,aligned,after,bound,arena⟩ := RequestHash.parsed_heap_shared input caller current actual bounded
  have same : pointer=root := by
    have value := Option.some.inj (stored.symm.trans heap)
    cases value
    rfl
  subst pointer
  exact ⟨aligned,after,bound,arena⟩

/-- Main's real32-byte root allocation leaves enough mapped scratch for the
entire original request-root hash, using the same decoded byte budget. -/
theorem geometry (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat→BitVec 64) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word root)))
    (requestLayout : Requests.Layout (Requests.offsetWord input (DecoderCall.requestStart input)) (BitVec.ofNat 64 (DecoderCall.requestLength input)))
    (requestImage : Requests.Image current (inputPointer+BitVec.ofNat 64 (DecoderCall.requestStart input)) (PayloadPrefix.finalCursor input)
      (BitVec.ofNat 64 (DecoderCall.requestLength input)) (Requests.offsetWord input (DecoderCall.requestStart input)) counts) :
    (description input counts).Layout inputPointer.toNat root.toNat (input.length%2^64) ∧
      (description input counts).RuntimeGeometry (input.length%2^64) (PersistentAlloc.rounded root 32#64) ∧
      PayloadHash.FinalPhase.OutputGeometry root root.toNat ∧
      (PersistentAlloc.rounded root 32#64).toNat=root.toNat+32 := by
  obtain ⟨aligned,after,bound,arena⟩ := frontier input caller current root actual bounded heap
  have currentLayout := layout input caller current counts root actual bounded after requestLayout requestImage
  have scratch := (description input counts).scratch_bound inputPointer.toNat root.toNat (input.length%2^64) currentLayout
  have room : root.toNat+(32#64).toNat+7<2^64 := by have h:=arena.upper; change root.toNat+32+7<2^64; omega
  have number : (PersistentAlloc.rounded root 32#64).toNat=root.toNat+32 := by
    rw [PersistentAlloc.rounded_nat root 32#64 room]
    change (root.toNat+32+7)/8*8=root.toNat+32
    omega
  have upper : DecoderSetup.cursor input≤2847949152 := (input_cursor_bounds input bounded).2.1
  have inputBound : input.length%2^64≤134217712 := bounded
  refine ⟨currentLayout,⟨⟨?_,?_⟩,?_⟩,⟨arena,aligned,Nat.le_refl _⟩,number⟩
  · rw [number]; have h:=arena.lower; omega
  · rw [number]; omega
  · rw [number]; omega

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.frontier
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.geometry
