import InitECandidate.Solver.GasBudget.ExponentLoop
import InitECandidate.Solver.Input.RlpWrite.LengthNormal

namespace InitECandidate.Solver.GasBudget.Exponent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

theorem bits_signature : ArithmeticEffects.Kind.u256_bit_length.signature = (U256Bits.formals, U256Bits.body, .one) := by
  simp only [ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, U256Bits.formals, U256Bits.body,
    U256Value.tupleShape, Guest.guestFn_u256_bit_length, declToHOL, shapeToHOL, List.map_cons, List.map_nil]

theorem bit_signature : ArithmeticEffects.Kind.bit_length64.signature = (BitLength.formals, BitLength.body, .one) := by
  simp only [ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original, BitLength.formals, BitLength.body,
    Guest.guestFn_bit_length64, declToHOL, shapeToHOL, List.map_cons, List.map_nil]

theorem after_length_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : ArithmeticEffects.Environment source.code) (length : Nat) (small : length ≤ 256)
    (len : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source afterLength).2.clock ≤ 19 * length := by
  let entry := bind source "t" 0#64
  have t : entry.locals.lookup (ofString "t") = some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have n : entry.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other _ "t" "len" _ (by decide)).trans len
  have cost := loop_price entry environment 0#64 length small t n (by simp)
  let output := evaluateHOLFiniteState entry (.seq loop (.return (localVar "result")))
  have actual := Input.ScalarScope.declare_execute source output.2 "t" (.const 0#64) 0#64
    (.seq loop (.return (localVar "result"))) output.1 rfl rfl
  rw [afterLength, actual]
  change source.clock - (evaluateHOLFiniteState entry (.seq loop (.return (localVar "result")))).2.clock ≤ 19 * length
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState entry loop = loopOutput at cost ⊢
  obtain ⟨result, target⟩ := loopOutput
  change source.clock - target.clock ≤ 19 * length at cost
  cases result with
  | none =>
    rw [Input.QuietClock.returned target.code (localVar "result") target rfl]
    exact cost
  | some result => exact cost

/-- The real length call costs two source clocks, and its actual returned
length is at most256. This prices the complete continuation at every clock
and every outcome, with no caller-funding or future-run premise. -/
theorem length_call_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : ArithmeticEffects.Environment source.code) (words : U256Value.Words)
    (b : source.locals.lookup (ofString "b") = some (U256Value.tuple words)) :
    source.clock - (evaluateHOLFiniteState source
      (.decCall (ofString "len") .one (ofString "u256_bit_length") [localVar "b"] afterLength)).2.clock ≤ 4866 := by
  classical
  by_cases enough : 2 ≤ source.clock
  · have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "b"] =
        some [U256Value.tuple words] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, b]
    have bitsCode := environment .u256_bit_length
    rw [bits_signature] at bitsCode
    have bitCode := environment .bit_length64
    rw [bit_signature] at bitCode
    obtain ⟨length, small, actual⟩ := U256Bits.call_execute source words "len" [localVar "b"] afterLength args bitsCode bitCode enough
    rw [actual]
    let entry := bind {source with clock := source.clock - 1 - 1} "len" (BitVec.ofNat 64 length)
    have len : entry.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := bind_lookup_same _ _ _
    have cost := after_length_price entry environment length small len
    have clock := evaluateHOLFiniteState_clock_le entry afterLength
    change source.clock - (evaluateHOLFiniteState entry afterLength).2.clock ≤ 4866
    change source.clock - 1 - 1 - (evaluateHOLFiniteState entry afterLength).2.clock ≤ 19 * length at cost
    change (evaluateHOLFiniteState entry afterLength).2.clock ≤ source.clock - 1 - 1 at clock
    omega
  · omega

end InitECandidate.Solver.GasBudget.Exponent

#print axioms InitECandidate.Solver.GasBudget.Exponent.bits_signature
#print axioms InitECandidate.Solver.GasBudget.Exponent.bit_signature
#print axioms InitECandidate.Solver.GasBudget.Exponent.after_length_price
#print axioms InitECandidate.Solver.GasBudget.Exponent.length_call_price
