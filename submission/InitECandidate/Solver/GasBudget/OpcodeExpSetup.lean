import InitECandidate.Solver.GasBudget.OpcodeExpProgram
import InitECandidate.Solver.GasBudget.ExponentPrice
import InitECandidate.Solver.GasBudget.StackPopsException
import InitECandidate.Solver.Input.OriginalExceptions

namespace InitECandidate.Solver.GasBudget.OpcodeExp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

theorem byte_signature : ArithmeticEffects.Kind.u256_byte_length.signature = (U256ByteLength.formals, U256ByteLength.body, .one) := by
  simp only [ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, U256ByteLength.formals, U256ByteLength.body,
    U256Value.tupleShape, Guest.guestFn_u256_byte_length, shapeToHOL, List.map_cons, List.map_nil]

theorem length_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_byte_length") = some (U256ByteLength.formals, U256ByteLength.body, .one) ∧
    code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one) ∧
    code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one) := by
  have environment := OriginalCodeEnvironment.arithmetic code installed
  have bytes := environment .u256_byte_length
  have bits := environment .u256_bit_length
  have bit := environment .bit_length64
  rw [byte_signature] at bytes
  rw [Exponent.bits_signature] at bits
  rw [Exponent.bit_signature] at bit
  exact ⟨bytes, bits, bit⟩

/-- Actual original pops and byte-length computation reach the dynamic
charge with a real <=32 byte count and exactly five paid source clocks. -/
theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ bytes ready inner, bytes ≤ 32 ∧ StackPop.PrefixEffect source ready frame 5 ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] (amount bytes) suffix) = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at normal
  obtain ⟨popped, scopedPost, fits, clock, fields, restRun, scopeEq, budget, used, outside, depth⟩ :=
    StackPop.pops_normal names source post frame _ (OriginalCodeEnvironment.stack_pop source.code installed) ev value normal
  have before : StackPop.PrefixEffect source popped frame 2 :=
    ⟨fits, clock, by rw [clock]; exact fields, budget, used, outside⟩
  have codeEq := congrArg PanSemStateFiniteExact.code fields
  change popped.code = source.code at codeEq
  have original : Input.OriginalCode.Installed popped.code := by rw [codeEq]; exact installed
  obtain ⟨bytesCode, bitsCode, bitCode⟩ := length_code popped.code original
  obtain ⟨bytes, inner, small, funded, run, postEq⟩ :=
    ByteLengthCall.normal popped scopedPost "nb" [localVar "exponent"] afterBytes bytesCode bitsCode bitCode value restRun
  let ready := bind {popped with clock := popped.clock - 3} "nb" (BitVec.ofNat 64 bytes)
  have afterLength : StackPop.PrefixEffect popped ready frame 3 := StackPop.PrefixEffect.unchanged popped ready frame 3 funded rfl rfl
  have nb : ready.locals.lookup (ofString "nb") = some (.val (.word (BitVec.ofNat 64 bytes))) := bind_lookup_same _ _ _
  rw [charge_choice ready bytes nb] at run
  refine ⟨bytes, ready, inner, small, before.trans afterLength, depth, run, ?_⟩
  rw [scopeEq, postEq]
  rfl

/-- Before the real dynamic charge, only actual pop underflow can escape
as an exception. Otherwise the genuine exceptional continuation is reached
after the same five-clock pure setup and checked byte count. -/
theorem setup_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ 2 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ bytes ready inner, bytes ≤ 32 ∧ StackPop.PrefixEffect source ready frame 5 ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] (amount bytes) suffix) = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  rcases StackPop.pops_exception names source post frame sp _ (OriginalCodeEnvironment.stack_pop source.code installed)
      ev mapped cell (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload run with failed | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := failed
    exact Or.inl ⟨sp.toNat + 1, bound, effect⟩
  · obtain ⟨popped, scopedPost, remaining, before, remainingCell, depth, restRun, scopeEq⟩ := continued
    have codeEq := congrArg PanSemStateFiniteExact.code before.fields
    change popped.code = source.code at codeEq
    have original : Input.OriginalCode.Installed popped.code := by rw [codeEq]; exact installed
    obtain ⟨bytesCode, bitsCode, bitCode⟩ := length_code popped.code original
    obtain ⟨bytes, inner, small, funded, run, postEq⟩ :=
      ByteLengthCall.exception popped scopedPost "nb" [localVar "exponent"] afterBytes bytesCode bitsCode bitCode identifier payload restRun
    let ready := bind {popped with clock := popped.clock - 3} "nb" (BitVec.ofNat 64 bytes)
    have afterLength : StackPop.PrefixEffect popped ready frame 3 := StackPop.PrefixEffect.unchanged popped ready frame 3 funded rfl rfl
    have nb : ready.locals.lookup (ofString "nb") = some (.val (.word (BitVec.ofNat 64 bytes))) := bind_lookup_same _ _ _
    rw [charge_choice ready bytes nb] at run
    refine Or.inr ⟨bytes, ready, inner, small, before.trans afterLength, run, ?_⟩
    rw [scopeEq, postEq]
    rfl

end InitECandidate.Solver.GasBudget.OpcodeExp

#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.length_code
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.setup_normal
#print axioms InitECandidate.Solver.GasBudget.OpcodeExp.setup_exception
