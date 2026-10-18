import InitECandidate.Solver.GasBudget.ArithmeticQuietClock
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

-- Every optional price is checked against its unchanged original body.
def Kind.fixedPrice : Kind → Option Nat
  | .add_sat => some 0
  | .bit_length64 => some 0
  | .bswap64 => some 0
  | .ceil_log2 => none
  | .digits_len => none
  | .digits_to_u256 => some 0
  | .div64by32 => none
  | .max => some 0
  | .min => some 0
  | .mul64x64 => some 0
  | .nlz32 => some 0
  | .sat_word => some 0
  | .u256_add => some 0
  | .u256_add_carry => some 0
  | .u256_and => some 0
  | .u256_eq => some 0
  | .u256_fits_word => some 0
  | .u256_from_word => some 0
  | .u256_is_zero => some 0
  | .u256_limb => some 0
  | .u256_low => some 0
  | .u256_lt => some 0
  | .u256_neg => some 0
  | .u256_not => some 0
  | .u256_or => some 0
  | .u256_shl => some 0
  | .u256_shr => some 0
  | .u256_slt => some 0
  | .u256_sub => some 0
  | .u256_xor => some 0
  | .u256_abs => some 1
  | .u256_bit => some 1
  | .u256_bit_length => some 4
  | .u256_byte => some 1
  | .u256_cmp => some 2
  | .u256_from_be => none
  | .u256_gt => some 1
  | .u256_mul => some 7
  | .u256_mul_full => some 16
  | .u256_sar => some 3
  | .u256_sgt => some 1
  | .u256_byte_length => some 5
  | .u256_exp => none
  | .u256_signextend => some 6

theorem price_add_sat (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.add_sat.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .add_sat code rfl)

theorem price_bit_length64 (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.bit_length64.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .bit_length64 code rfl)

theorem price_bswap64 (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.bswap64.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .bswap64 code rfl)

theorem price_digits_to_u256 (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.digits_to_u256.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .digits_to_u256 code rfl)

theorem price_max (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.max.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .max code rfl)

theorem price_min (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.min.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .min code rfl)

theorem price_mul64x64 (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.mul64x64.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .mul64x64 code rfl)

theorem price_nlz32 (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.nlz32.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .nlz32 code rfl)

theorem price_sat_word (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.sat_word.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .sat_word code rfl)

theorem price_u256_add (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_add.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_add code rfl)

theorem price_u256_add_carry (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_add_carry.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_add_carry code rfl)

theorem price_u256_and (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_and.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_and code rfl)

theorem price_u256_eq (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_eq.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_eq code rfl)

theorem price_u256_fits_word (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_fits_word.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_fits_word code rfl)

theorem price_u256_from_word (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_from_word.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_from_word code rfl)

theorem price_u256_is_zero (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_is_zero.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_is_zero code rfl)

theorem price_u256_limb (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_limb.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_limb code rfl)

theorem price_u256_low (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_low.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_low code rfl)

theorem price_u256_lt (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_lt.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_lt code rfl)

theorem price_u256_neg (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_neg.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_neg code rfl)

theorem price_u256_not (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_not.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_not code rfl)

theorem price_u256_or (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_or.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_or code rfl)

theorem price_u256_shl (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_shl.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_shl code rfl)

theorem price_u256_shr (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_shr.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_shr code rfl)

theorem price_u256_slt (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_slt.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_slt code rfl)

theorem price_u256_sub (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_sub.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_sub code rfl)

theorem price_u256_xor (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_xor.body 0 := by
  exact Input.ClockCost.of_quiet code _ (quiet_preserves .u256_xor code rfl)

theorem price_u256_abs (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_abs.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_abs, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 1 0
  · apply Input.ClockCost.conditional code _ _ _ 1 0
    · exact Input.ClockCost.call_body code none (ofString "u256_neg") _ _ _ _ 0 (environment .u256_neg) (price_u256_neg code environment)
    · exact Input.ClockCost.skip code
  · exact Input.ClockCost.returned code _

theorem price_u256_bit (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_bit.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_bit, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 0 1
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "u256_limb") _ _ _ _ _ 0 0 (environment .u256_limb) (price_u256_limb code environment) ?_
    exact Input.ClockCost.returned code _

theorem price_u256_bit_length (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_bit_length.body 4 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_bit_length, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 1 3
  · apply Input.ClockCost.conditional code _ _ _ 1 0
    · refine Input.ClockCost.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ 0 0 (environment .bit_length64) (price_bit_length64 code environment) ?_
      exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · apply Input.ClockCost.sequence code _ _ 1 2
    · apply Input.ClockCost.conditional code _ _ _ 1 0
      · refine Input.ClockCost.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ 0 0 (environment .bit_length64) (price_bit_length64 code environment) ?_
        exact Input.ClockCost.returned code _
      · exact Input.ClockCost.skip code
    · apply Input.ClockCost.sequence code _ _ 1 1
      · apply Input.ClockCost.conditional code _ _ _ 1 0
        · refine Input.ClockCost.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ 0 0 (environment .bit_length64) (price_bit_length64 code environment) ?_
          exact Input.ClockCost.returned code _
        · exact Input.ClockCost.skip code
      · exact Input.ClockCost.call_body code none (ofString "bit_length64") _ _ _ _ 0 (environment .bit_length64) (price_bit_length64 code environment)

theorem price_u256_byte (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_byte.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_byte, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 0 1
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · apply Input.ClockCost.declared code _ _ _ _ 1
    refine Input.ClockCost.scoped_body code _ _ (ofString "u256_limb") _ _ _ _ _ 0 0 (environment .u256_limb) (price_u256_limb code environment) ?_
    exact Input.ClockCost.returned code _

theorem price_u256_cmp (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_cmp.body 2 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_cmp, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "u256_lt") _ _ _ _ _ 0 1 (environment .u256_lt) (price_u256_lt code environment) ?_
  apply Input.ClockCost.sequence code _ _ 0 1
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "u256_eq") _ _ _ _ _ 0 0 (environment .u256_eq) (price_u256_eq code environment) ?_
    apply Input.ClockCost.sequence code _ _ 0 0
    · apply Input.ClockCost.conditional code _ _ _ 0 0
      · exact Input.ClockCost.returned code _
      · exact Input.ClockCost.skip code
    · exact Input.ClockCost.returned code _

theorem price_u256_gt (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_gt.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_gt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.ClockCost.call_body code none (ofString "u256_lt") _ _ _ _ 0 (environment .u256_lt) (price_u256_lt code environment)

theorem price_u256_mul (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_mul.body 7 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_mul, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 1 6
  · apply Input.ClockCost.conditional code _ _ _ 1 0
    · refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 0 (environment .mul64x64) (price_mul64x64 code environment) ?_
      exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 5 (environment .mul64x64) (price_mul64x64 code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 4 (environment .mul64x64) (price_mul64x64 code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 3 (environment .mul64x64) (price_mul64x64 code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 2 (environment .mul64x64) (price_mul64x64 code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 1 (environment .mul64x64) (price_mul64x64 code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 0 (environment .mul64x64) (price_mul64x64 code environment) ?_
    apply Input.ClockCost.declared code _ _ _ _ 0
    apply Input.ClockCost.declared code _ _ _ _ 0
    apply Input.ClockCost.declared code _ _ _ _ 0
    apply Input.ClockCost.declared code _ _ _ _ 0
    apply Input.ClockCost.sequence code _ _ 0 0
    · exact Input.ClockCost.assign code _ _
    · apply Input.ClockCost.sequence code _ _ 0 0
      · exact Input.ClockCost.primitive code _ _ _
      · apply Input.ClockCost.sequence code _ _ 0 0
        · exact Input.ClockCost.assign code _ _
        · apply Input.ClockCost.sequence code _ _ 0 0
          · exact Input.ClockCost.assign code _ _
          · apply Input.ClockCost.sequence code _ _ 0 0
            · exact Input.ClockCost.primitive code _ _ _
            · apply Input.ClockCost.sequence code _ _ 0 0
              · exact Input.ClockCost.assign code _ _
              · apply Input.ClockCost.sequence code _ _ 0 0
                · exact Input.ClockCost.assign code _ _
                · apply Input.ClockCost.declared code _ _ _ _ 0
                  apply Input.ClockCost.sequence code _ _ 0 0
                  · exact Input.ClockCost.assign code _ _
                  · apply Input.ClockCost.sequence code _ _ 0 0
                    · exact Input.ClockCost.assign code _ _
                    · apply Input.ClockCost.sequence code _ _ 0 0
                      · exact Input.ClockCost.primitive code _ _ _
                      · apply Input.ClockCost.sequence code _ _ 0 0
                        · exact Input.ClockCost.assign code _ _
                        · apply Input.ClockCost.sequence code _ _ 0 0
                          · exact Input.ClockCost.assign code _ _
                          · apply Input.ClockCost.sequence code _ _ 0 0
                            · exact Input.ClockCost.primitive code _ _ _
                            · apply Input.ClockCost.sequence code _ _ 0 0
                              · exact Input.ClockCost.assign code _ _
                              · apply Input.ClockCost.sequence code _ _ 0 0
                                · exact Input.ClockCost.assign code _ _
                                · apply Input.ClockCost.sequence code _ _ 0 0
                                  · exact Input.ClockCost.primitive code _ _ _
                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                    · exact Input.ClockCost.assign code _ _
                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                      · exact Input.ClockCost.assign code _ _
                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                        · exact Input.ClockCost.primitive code _ _ _
                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                          · exact Input.ClockCost.assign code _ _
                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                            · exact Input.ClockCost.assign code _ _
                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                              · exact Input.ClockCost.primitive code _ _ _
                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                · exact Input.ClockCost.assign code _ _
                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                  · exact Input.ClockCost.assign code _ _
                                                  · apply Input.ClockCost.declared code _ _ _ _ 0
                                                    apply Input.ClockCost.sequence code _ _ 0 0
                                                    · exact Input.ClockCost.assign code _ _
                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                      · exact Input.ClockCost.assign code _ _
                                                      · apply Input.ClockCost.declared code _ _ _ _ 0
                                                        exact Input.ClockCost.returned code _

theorem price_u256_mul_full (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_mul_full.body 16 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_mul_full, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 15 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 14 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 13 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 12 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 11 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 10 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 9 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 8 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 7 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 6 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 5 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 4 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 3 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 2 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 1 (environment .mul64x64) (price_mul64x64 code environment) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ 0 0 (environment .mul64x64) (price_mul64x64 code environment) ?_
  apply Input.ClockCost.declared code _ _ _ _ 0
  apply Input.ClockCost.declared code _ _ _ _ 0
  apply Input.ClockCost.declared code _ _ _ _ 0
  apply Input.ClockCost.declared code _ _ _ _ 0
  apply Input.ClockCost.sequence code _ _ 0 0
  · exact Input.ClockCost.assign code _ _
  · apply Input.ClockCost.sequence code _ _ 0 0
    · exact Input.ClockCost.primitive code _ _ _
    · apply Input.ClockCost.sequence code _ _ 0 0
      · exact Input.ClockCost.assign code _ _
      · apply Input.ClockCost.sequence code _ _ 0 0
        · exact Input.ClockCost.assign code _ _
        · apply Input.ClockCost.sequence code _ _ 0 0
          · exact Input.ClockCost.primitive code _ _ _
          · apply Input.ClockCost.sequence code _ _ 0 0
            · exact Input.ClockCost.assign code _ _
            · apply Input.ClockCost.sequence code _ _ 0 0
              · exact Input.ClockCost.assign code _ _
              · apply Input.ClockCost.declared code _ _ _ _ 0
                apply Input.ClockCost.sequence code _ _ 0 0
                · exact Input.ClockCost.assign code _ _
                · apply Input.ClockCost.sequence code _ _ 0 0
                  · exact Input.ClockCost.assign code _ _
                  · apply Input.ClockCost.sequence code _ _ 0 0
                    · exact Input.ClockCost.primitive code _ _ _
                    · apply Input.ClockCost.sequence code _ _ 0 0
                      · exact Input.ClockCost.assign code _ _
                      · apply Input.ClockCost.sequence code _ _ 0 0
                        · exact Input.ClockCost.assign code _ _
                        · apply Input.ClockCost.sequence code _ _ 0 0
                          · exact Input.ClockCost.primitive code _ _ _
                          · apply Input.ClockCost.sequence code _ _ 0 0
                            · exact Input.ClockCost.assign code _ _
                            · apply Input.ClockCost.sequence code _ _ 0 0
                              · exact Input.ClockCost.assign code _ _
                              · apply Input.ClockCost.sequence code _ _ 0 0
                                · exact Input.ClockCost.primitive code _ _ _
                                · apply Input.ClockCost.sequence code _ _ 0 0
                                  · exact Input.ClockCost.assign code _ _
                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                    · exact Input.ClockCost.assign code _ _
                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                      · exact Input.ClockCost.primitive code _ _ _
                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                        · exact Input.ClockCost.assign code _ _
                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                          · exact Input.ClockCost.assign code _ _
                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                            · exact Input.ClockCost.primitive code _ _ _
                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                              · exact Input.ClockCost.assign code _ _
                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                · exact Input.ClockCost.assign code _ _
                                                · apply Input.ClockCost.declared code _ _ _ _ 0
                                                  apply Input.ClockCost.sequence code _ _ 0 0
                                                  · exact Input.ClockCost.assign code _ _
                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                    · exact Input.ClockCost.assign code _ _
                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                      · exact Input.ClockCost.primitive code _ _ _
                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                        · exact Input.ClockCost.assign code _ _
                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                          · exact Input.ClockCost.assign code _ _
                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                            · exact Input.ClockCost.primitive code _ _ _
                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                              · exact Input.ClockCost.assign code _ _
                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                · exact Input.ClockCost.assign code _ _
                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                  · exact Input.ClockCost.primitive code _ _ _
                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                    · exact Input.ClockCost.assign code _ _
                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                      · exact Input.ClockCost.assign code _ _
                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                        · exact Input.ClockCost.primitive code _ _ _
                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                          · exact Input.ClockCost.assign code _ _
                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                            · exact Input.ClockCost.assign code _ _
                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                              · exact Input.ClockCost.primitive code _ _ _
                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                · exact Input.ClockCost.assign code _ _
                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                    · exact Input.ClockCost.primitive code _ _ _
                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                          · exact Input.ClockCost.primitive code _ _ _
                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                              · apply Input.ClockCost.declared code _ _ _ _ 0
                                                                                                apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                · exact Input.ClockCost.assign code _ _
                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                    · exact Input.ClockCost.primitive code _ _ _
                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                          · exact Input.ClockCost.primitive code _ _ _
                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                · exact Input.ClockCost.primitive code _ _ _
                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                    · exact Input.ClockCost.assign code _ _
                                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                      · exact Input.ClockCost.primitive code _ _ _
                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                          · exact Input.ClockCost.assign code _ _
                                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                            · exact Input.ClockCost.primitive code _ _ _
                                                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                · exact Input.ClockCost.assign code _ _
                                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                  · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                    · exact Input.ClockCost.assign code _ _
                                                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                        · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                          · exact Input.ClockCost.assign code _ _
                                                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                                                                            · apply Input.ClockCost.declared code _ _ _ _ 0
                                                                                                                                              apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                · exact Input.ClockCost.assign code _ _
                                                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                  · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                    · exact Input.ClockCost.assign code _ _
                                                                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                        · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                          · exact Input.ClockCost.assign code _ _
                                                                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                              · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                · exact Input.ClockCost.assign code _ _
                                                                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                    · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                          · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                                                                                                              · apply Input.ClockCost.declared code _ _ _ _ 0
                                                                                                                                                                                apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                    · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                                                    · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                        · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                          · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                                                          · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                            · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                            · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                              · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                              · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                                · exact Input.ClockCost.primitive code _ _ _
                                                                                                                                                                                                · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                                  · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                                  · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                                    · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                                    · apply Input.ClockCost.declared code _ _ _ _ 0
                                                                                                                                                                                                      apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                                      · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                                      · apply Input.ClockCost.sequence code _ _ 0 0
                                                                                                                                                                                                        · exact Input.ClockCost.assign code _ _
                                                                                                                                                                                                        · apply Input.ClockCost.declared code _ _ _ _ 0
                                                                                                                                                                                                          exact Input.ClockCost.returned code _

theorem price_u256_sar (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_sar.body 3 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sar, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.declared code _ _ _ _ 3
  apply Input.ClockCost.sequence code _ _ 0 3
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · apply Input.ClockCost.sequence code _ _ 0 0
      · apply Input.ClockCost.conditional code _ _ _ 0 0
        · exact Input.ClockCost.returned code _
        · exact Input.ClockCost.skip code
      · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · refine Input.ClockCost.scoped_body code _ _ (ofString "u256_shr") _ _ _ _ _ 0 2 (environment .u256_shr) (price_u256_shr code environment) ?_
    apply Input.ClockCost.sequence code _ _ 2 0
    · apply Input.ClockCost.conditional code _ _ _ 2 0
      · apply Input.ClockCost.conditional code _ _ _ 2 0
        · refine Input.ClockCost.scoped_body code _ _ (ofString "u256_shl") _ _ _ _ _ 0 1 (environment .u256_shl) (price_u256_shl code environment) ?_
          exact Input.ClockCost.call_body code (some (some _)) (ofString "u256_or") _ _ _ _ 0 (environment .u256_or) (price_u256_or code environment)
        · exact Input.ClockCost.skip code
      · exact Input.ClockCost.skip code
    · exact Input.ClockCost.returned code _

theorem price_u256_sgt (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_sgt.body 1 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sgt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.ClockCost.call_body code none (ofString "u256_slt") _ _ _ _ 0 (environment .u256_slt) (price_u256_slt code environment)

theorem price_u256_byte_length (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_byte_length.body 5 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_byte_length, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.ClockCost.scoped_body code _ _ (ofString "u256_bit_length") _ _ _ _ _ 4 0 (environment .u256_bit_length) (price_u256_bit_length code environment) ?_
  exact Input.ClockCost.returned code _

theorem price_u256_signextend (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.u256_signextend.body 6 := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_signextend, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.sequence code _ _ 0 6
  · apply Input.ClockCost.conditional code _ _ _ 0 0
    · exact Input.ClockCost.returned code _
    · exact Input.ClockCost.skip code
  · apply Input.ClockCost.declared code _ _ _ _ 6
    refine Input.ClockCost.scoped_body code _ _ (ofString "u256_bit") _ _ _ _ _ 1 4 (environment .u256_bit) (price_u256_bit code environment) ?_
    refine Input.ClockCost.scoped_body code _ _ (ofString "u256_shl") _ _ _ _ _ 0 3 (environment .u256_shl) (price_u256_shl code environment) ?_
    apply Input.ClockCost.sequence code _ _ 1 2
    · apply Input.ClockCost.conditional code _ _ _ 1 0
      · exact Input.ClockCost.call_body code none (ofString "u256_or") _ _ _ _ 0 (environment .u256_or) (price_u256_or code environment)
      · exact Input.ClockCost.skip code
    · refine Input.ClockCost.scoped_body code _ _ (ofString "u256_not") _ _ _ _ _ 0 1 (environment .u256_not) (price_u256_not code environment) ?_
      exact Input.ClockCost.call_body code none (ofString "u256_and") _ _ _ _ 0 (environment .u256_and) (price_u256_and code environment)

theorem fixed_price (kind : Kind) (price : Nat) (code) (environment : Environment code)
    (checked : kind.fixedPrice = some price) : Input.ClockCost.Bound code kind.body price := by
  cases kind with
  | add_sat =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_add_sat code environment
  | bit_length64 =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_bit_length64 code environment
  | bswap64 =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_bswap64 code environment
  | ceil_log2 => cases checked
  | digits_len => cases checked
  | digits_to_u256 =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_digits_to_u256 code environment
  | div64by32 => cases checked
  | max =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_max code environment
  | min =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_min code environment
  | mul64x64 =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_mul64x64 code environment
  | nlz32 =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_nlz32 code environment
  | sat_word =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_sat_word code environment
  | u256_add =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_add code environment
  | u256_add_carry =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_add_carry code environment
  | u256_and =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_and code environment
  | u256_eq =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_eq code environment
  | u256_fits_word =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_fits_word code environment
  | u256_from_word =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_from_word code environment
  | u256_is_zero =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_is_zero code environment
  | u256_limb =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_limb code environment
  | u256_low =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_low code environment
  | u256_lt =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_lt code environment
  | u256_neg =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_neg code environment
  | u256_not =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_not code environment
  | u256_or =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_or code environment
  | u256_shl =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_shl code environment
  | u256_shr =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_shr code environment
  | u256_slt =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_slt code environment
  | u256_sub =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_sub code environment
  | u256_xor =>
    have equal : price = 0 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_xor code environment
  | u256_abs =>
    have equal : price = 1 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_abs code environment
  | u256_bit =>
    have equal : price = 1 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_bit code environment
  | u256_bit_length =>
    have equal : price = 4 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_bit_length code environment
  | u256_byte =>
    have equal : price = 1 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_byte code environment
  | u256_cmp =>
    have equal : price = 2 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_cmp code environment
  | u256_from_be => cases checked
  | u256_gt =>
    have equal : price = 1 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_gt code environment
  | u256_mul =>
    have equal : price = 7 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_mul code environment
  | u256_mul_full =>
    have equal : price = 16 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_mul_full code environment
  | u256_sar =>
    have equal : price = 3 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_sar code environment
  | u256_sgt =>
    have equal : price = 1 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_sgt code environment
  | u256_byte_length =>
    have equal : price = 5 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_byte_length code environment
  | u256_exp => cases checked
  | u256_signextend =>
    have equal : price = 6 := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm
    subst price
    exact price_u256_signextend code environment

/-- Actual source clocks spent, for every real helper outcome.
These are call/loop units and omit straight-line target instructions. -/
theorem fixed_clock_spent (kind : Kind) (price : Nat) (checked : kind.fixedPrice = some price)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : Environment source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.body = (outcome, target)) :
    source.clock - target.clock ≤ price := by
  have cost := fixed_price kind price source.code environment checked source rfl
  simpa only [run] using cost

theorem fixed_call_spent (kind : Kind) (price : Nat) (checked : kind.fixedPrice = some price)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : Environment source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) kind.name arguments) = (outcome, target)) :
    source.clock - target.clock ≤ price + 1 := by
  have bound := Input.ClockCost.call_body source.code destination kind.name arguments kind.signature.1 kind.body kind.signature.2.2 price
    (environment kind) (fixed_price kind price source.code environment checked)
  have actual := bound source rfl
  simpa only [run] using actual

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_price
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_clock_spent
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_call_spent
