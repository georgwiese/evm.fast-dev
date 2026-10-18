import InitECandidate.Solver.Input.RlpWrite.U256ByteLength
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.RlpWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Recover a known pure return contract from an actual successful run,
without assuming its caller supplied enough source clock. -/
theorem normal_of_funded (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (body : ProgHOL 64) (price bound : Nat) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned value), post))
    (funded : ∀ entry : PanSemStateFiniteExact 64 Guest.HostMemory,
      entry.locals = source.locals → entry.code = source.code → price ≤ entry.clock →
      ∃ target number, number ≤ bound ∧
        evaluateHOLFiniteState entry body = (some (.returned (.val (.word (BitVec.ofNat 64 number)))), target) ∧
        emptyLocalsHOLFinite target = emptyLocalsHOLFinite {entry with clock := entry.clock - price}) :
    ∃ number, number ≤ bound ∧ value = .val (.word (BitVec.ofNat 64 number)) ∧
      price ≤ source.clock ∧ post.clock = source.clock - price ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - price} := by
  have shifted := panPropsEvaluateAddClockEq body source (some (.returned value)) post price
    ⟨normal, by intro impossible; cases impossible⟩
  obtain ⟨target, number, bounded, run, frame⟩ :=
    funded {source with clock := source.clock + price} rfl rfl (by change price ≤ source.clock + price; omega)
  have resultEq := congrArg Prod.fst (shifted.symm.trans run)
  have valueEq : value = .val (.word (BitVec.ofNat 64 number)) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  have stateEq := congrArg Prod.snd (shifted.symm.trans run)
  change {post with clock := post.clock + price} = target at stateEq
  rw [← stateEq] at frame
  have clockEq := congrArg PanSemStateFiniteExact.clock frame
  change post.clock + price = source.clock + price - price at clockEq
  have fields := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with clock := state.clock - price}) frame
  have frameEq : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - price} := by
    simpa only [emptyLocalsHOLFinite, Nat.add_sub_cancel] using fields
  exact ⟨number, bounded, valueEq, by omega, by omega, frameEq⟩

theorem U256Bits.normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (a : source.locals.lookup (ofString "a") = some (U256Value.tuple words))
    (code : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source U256Bits.body = (some (.returned value), post)) :
    ∃ bits, bits ≤ 256 ∧ value = .val (.word (BitVec.ofNat 64 bits)) ∧
      1 ≤ source.clock ∧ post.clock = source.clock - 1 ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  apply normal_of_funded source post _ 1 256 value run
  intro entry locals codeEq enough
  exact U256Bits.execute entry words (by rw [locals]; exact a) (by rw [codeEq]; exact code) enough

theorem U256ByteLength.normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (a : source.locals.lookup (ofString "a") = some (U256Value.tuple words))
    (code : source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one))
    (bitCode : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source U256ByteLength.body = (some (.returned value), post)) :
    ∃ bytes, bytes ≤ 32 ∧ value = .val (.word (BitVec.ofNat 64 bytes)) ∧
      2 ≤ source.clock ∧ post.clock = source.clock - 2 ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 2} := by
  apply normal_of_funded source post _ 2 32 value run
  intro entry locals codeEq enough
  exact U256ByteLength.execute entry words (by rw [locals]; exact a)
    (by rw [codeEq]; exact code) (by rw [codeEq]; exact bitCode) enough

end InitECandidate.Solver.Input.RlpWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.normal_of_funded
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Bits.normal
#print axioms InitECandidate.Solver.Input.RlpWrite.U256ByteLength.normal
