import InitECandidate.Solver.Input.MainWitnessGeometry
import InitECandidate.Solver.Input.Witness.OffsetsTrace
import InitECandidate.Solver.Input.Witness.OffsetValues

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Original witness offsets at the actually reached decoder state. This
retains the physical payload/request/SI images and supplies validated slices
for the three real byte-list calls, including every offset rejection. -/
theorem witness_offsets_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : WitnessEntry input source entry counts)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (minimum : 12 ≤ witnessLength input)
    (inside : witnessStart input + witnessLength input = input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Witness.offsetBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 510) ∨
    (Witness.offsetNat input (witnessStart input) 0 = 12 ∧ 12 ≤ Witness.offsetNat input (witnessStart input) 1 ∧
      Witness.offsetNat input (witnessStart input) 1 ≤ Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2 ≤ witnessLength input ∧
      ∃ next innerPost,WitnessEntry input source next counts 510 ∧
        (∀ position < 3,next.memory (byteAddress 2713715344#64 (8*position)) = .word (Witness.offsetWord input (witnessStart input) position)) ∧
        evaluateHOLFiniteState next Witness.loadedBody = (result,innerPost) ∧ post = restore entry "i" innerPost) := by
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  have upper : inputPointer.toNat + input.length % 2^64 + 8 ≤ 33806089496 := by
    change 2713731432 + input.length % 2^64 + 8 ≤ _
    have small : input.length % 2^64 ≤ 134217712 := bounded
    omega
  have offsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := (actual.globals _ (by decide)).trans environment.offsets
  have shape : entry.eshapes.lookup (ofString "SszErr") = some .one := by rw [actual.exceptions]; exact environment.shapes .SszErr
  rcases Witness.offsets_trace entry post input inputPointer 2713715344#64 (BitVec.ofNat 64 (witnessLength input)) (witnessStart input)
    actual.bytes (by omega) actual.pointer actual.length offsets (actual.domain.trans environment.domain) (by decide) (by decide) (by decide) (by decide) upper
    (original_offsets_code entry.code installed) (original_fail_code entry.code installed) shape result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    have forward := evaluateHOLFiniteState_clock_le entry Witness.offsetBody
    rw [run] at forward
    change post.clock ≤ entry.clock at forward
    have before := actual.forward
    have prefixCost := actual.cost
    exact Or.inl ⟨error,allowed,same,by omega⟩
  · obtain ⟨first,valid,next,innerPost,forward,cost,control,bytes,other,cells,remaining,restored,memory⟩ := normal
    have totalNumber : (BitVec.ofNat 64 (witnessLength input)).toNat = witnessLength input := by
      have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    obtain ⟨firstNat,middleLower,ordered,lastUpper⟩ := Witness.offset_values input (witnessStart input) (BitVec.ofNat 64 (witnessLength input)) first valid
    rw [totalNumber] at lastUpper
    have globals : next.globals = entry.globals := by have h := congrArg PanSemStateFiniteExact.globals control; exact h
    have codes : next.code = entry.code := by have h := congrArg PanSemStateFiniteExact.code control; exact h
    have domains : next.memaddrs = entry.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs control; exact h
    have shapes : next.eshapes = entry.eshapes := by have h := congrArg PanSemStateFiniteExact.eshapes control; exact h
    have cursor := input_cursor_bounds input bounded
    have cursorLower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := cursor.1
    have cursorUpper : DecoderSetup.cursor input ≤ 2847949152 := cursor.2.1
    have previous := PayloadPrefix.final_cursor_geometry input bounded actual.transactions
    have small : input.length % 2^64 ≤ 134217712 := bounded
    have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := cursor.2.1; omega)]
    have plNat := (PayloadPrefix.cursor_number input bounded).1
    have earlier (base : BitVec 64) (offset : Nat) (lo : 2713731432 ≤ base.toNat) (hi : base.toNat + offset < 2^64) :
        next.memory (base + BitVec.ofNat 64 offset) = entry.memory (base + BitVec.ofNat 64 offset) := by
      apply memory
      right
      have address := byteAddress_toNat base offset hi
      change (base + BitVec.ofNat 64 offset).toNat = base.toNat + offset at address
      change 2713715344 + 24 ≤ _
      rw [address]
      omega
    have image : Requests.Image next (inputPointer + BitVec.ofNat 64 (requestStart input)) (PayloadPrefix.finalCursor input) (BitVec.ofNat 64 (requestLength input)) (Requests.offsetWord input (requestStart input)) counts := by
      constructor
      · intro index indexSmall
        have old := actual.requests.cells index indexSmall
        have lo : 2713731432 ≤ (PayloadPrefix.finalCursor input).toNat := by have := previous.2.2.1; have := cursor.1; omega
        have hi := previous.2.2.2
        exact ⟨(earlier _ (16*index) lo (by have := cursor.2.1; omega)).trans old.1,(earlier _ (16*index+8) lo (by have := cursor.2.1; omega)).trans old.2⟩
      · exact actual.requests.arithmetic
    have entryCost := actual.cost
    have entryForward := actual.forward
    have nextEntry : WitnessEntry input source next counts 510 := ⟨bytes,
      (other _ (by decide)).trans actual.pointer,(other _ (by decide)).trans actual.length,(other _ (by decide)).trans actual.si,
      codes.trans actual.code,domains.trans actual.domain,shapes.trans actual.exceptions,by rw [globals]; exact actual.heap,
      by intro key different; rw [globals]; exact actual.globals key different,
      (earlier _ 88 (by rw [plNat]; have := cursor.1; omega) (by rw [plNat]; have := cursor.2.1; omega)).trans actual.gasCell,
      (earlier _ 56 (by rw [plNat]; have := cursor.1; omega) (by rw [plNat]; have := cursor.2.1; omega)).trans actual.countCell,
      (earlier _ 32 (by rw [siNat]; have := cursor.1; omega) (by rw [siNat]; have := cursor.2.1; omega)).trans actual.requestCell,
      actual.requestLayout,image,actual.transactions,by omega,by omega⟩
    exact Or.inr ⟨firstNat,middleLower,ordered,lastUpper,next,innerPost,nextEntry,cells,remaining,restored⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_offsets_trace
