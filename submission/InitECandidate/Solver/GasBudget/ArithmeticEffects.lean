import InitECandidate.Solver.Input.LocalEffectsPrimitive

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.LocalEffects

attribute [local irreducible] Input.LocalEffects.Preserves

-- Untrusted candidate catalogue. Every original body is checked below.
inductive Kind where
  | add_sat
  | bit_length64
  | bswap64
  | ceil_log2
  | digits_len
  | digits_to_u256
  | div64by32
  | max
  | min
  | mul64x64
  | nlz32
  | sat_word
  | u256_add
  | u256_add_carry
  | u256_and
  | u256_eq
  | u256_fits_word
  | u256_from_word
  | u256_is_zero
  | u256_limb
  | u256_low
  | u256_lt
  | u256_neg
  | u256_not
  | u256_or
  | u256_shl
  | u256_shr
  | u256_slt
  | u256_sub
  | u256_xor
  | u256_abs
  | u256_bit
  | u256_bit_length
  | u256_byte
  | u256_cmp
  | u256_from_be
  | u256_gt
  | u256_mul
  | u256_mul_full
  | u256_sar
  | u256_sgt
  | u256_byte_length
  | u256_exp
  | u256_signextend

def Kind.original : Kind → Decl (BitVec 64)
  | .add_sat => Guest.guestFn_add_sat
  | .bit_length64 => Guest.guestFn_bit_length64
  | .bswap64 => Guest.guestFn_bswap64
  | .ceil_log2 => Guest.guestFn_ceil_log2
  | .digits_len => Guest.guestFn_digits_len
  | .digits_to_u256 => Guest.guestFn_digits_to_u256
  | .div64by32 => Guest.guestFn_div64by32
  | .max => Guest.guestFn_max
  | .min => Guest.guestFn_min
  | .mul64x64 => Guest.guestFn_mul64x64
  | .nlz32 => Guest.guestFn_nlz32
  | .sat_word => Guest.guestFn_sat_word
  | .u256_add => Guest.guestFn_u256_add
  | .u256_add_carry => Guest.guestFn_u256_add_carry
  | .u256_and => Guest.guestFn_u256_and
  | .u256_eq => Guest.guestFn_u256_eq
  | .u256_fits_word => Guest.guestFn_u256_fits_word
  | .u256_from_word => Guest.guestFn_u256_from_word
  | .u256_is_zero => Guest.guestFn_u256_is_zero
  | .u256_limb => Guest.guestFn_u256_limb
  | .u256_low => Guest.guestFn_u256_low
  | .u256_lt => Guest.guestFn_u256_lt
  | .u256_neg => Guest.guestFn_u256_neg
  | .u256_not => Guest.guestFn_u256_not
  | .u256_or => Guest.guestFn_u256_or
  | .u256_shl => Guest.guestFn_u256_shl
  | .u256_shr => Guest.guestFn_u256_shr
  | .u256_slt => Guest.guestFn_u256_slt
  | .u256_sub => Guest.guestFn_u256_sub
  | .u256_xor => Guest.guestFn_u256_xor
  | .u256_abs => Guest.guestFn_u256_abs
  | .u256_bit => Guest.guestFn_u256_bit
  | .u256_bit_length => Guest.guestFn_u256_bit_length
  | .u256_byte => Guest.guestFn_u256_byte
  | .u256_cmp => Guest.guestFn_u256_cmp
  | .u256_from_be => Guest.guestFn_u256_from_be
  | .u256_gt => Guest.guestFn_u256_gt
  | .u256_mul => Guest.guestFn_u256_mul
  | .u256_mul_full => Guest.guestFn_u256_mul_full
  | .u256_sar => Guest.guestFn_u256_sar
  | .u256_sgt => Guest.guestFn_u256_sgt
  | .u256_byte_length => Guest.guestFn_u256_byte_length
  | .u256_exp => Guest.guestFn_u256_exp
  | .u256_signextend => Guest.guestFn_u256_signextend

def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  match kind.original with
  | .function fn => (fn.params.map (fun pair => (ofString pair.1, shapeToHOL pair.2)), progToHOL fn.body, shapeToHOL fn.returnShape)
  | _ => ([], .skip, .one)

def Kind.body (kind : Kind) : ProgHOL 64 := kind.signature.2.1
def Kind.name (kind : Kind) : MlS := match kind.original with | .function fn => ofString fn.name | _ => ofString ""

def Environment (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ kind : Kind, code.lookup kind.name = some kind.signature

theorem pure_add_sat (code) (environment : Environment code) : Preserves code Kind.add_sat.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_add_sat, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_bit_length64 (code) (environment : Environment code) : Preserves code Kind.bit_length64.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_bit_length64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.assign code _ _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.skip code
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.skip code
          · apply Input.LocalEffects.sequence
            · apply Input.LocalEffects.conditional
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · exact Input.LocalEffects.assign code _ _
              · exact Input.LocalEffects.skip code
            · exact Input.LocalEffects.returned code _

theorem pure_bswap64 (code) (environment : Environment code) : Preserves code Kind.bswap64.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_bswap64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.assign code _ _
  · apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.assign code _ _
    · exact Input.LocalEffects.returned code _

theorem pure_ceil_log2 (code) (environment : Environment code) : Preserves code Kind.ceil_log2.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_ceil_log2, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.loop
    exact Input.LocalEffects.assign code _ _
  · exact Input.LocalEffects.returned code _

theorem pure_digits_len (code) (environment : Environment code) : Preserves code Kind.digits_len.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_digits_len, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.loop
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · exact Input.LocalEffects.assign code _ _
  · exact Input.LocalEffects.returned code _

theorem pure_digits_to_u256 (code) (environment : Environment code) : Preserves code Kind.digits_to_u256.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_digits_to_u256, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_div64by32 (code) (environment : Environment code) : Preserves code Kind.div64by32.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_div64by32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.loop
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.assign code _ _
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_max (code) (environment : Environment code) : Preserves code Kind.max.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_max, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_min (code) (environment : Environment code) : Preserves code Kind.min.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_min, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_mul64x64 (code) (environment : Environment code) : Preserves code Kind.mul64x64.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_mul64x64, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.primitive code _ _ _
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.declared
      exact Input.LocalEffects.returned code _

theorem pure_nlz32 (code) (environment : Environment code) : Preserves code Kind.nlz32.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_nlz32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.assign code _ _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.skip code
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.skip code
          · exact Input.LocalEffects.returned code _

theorem pure_sat_word (code) (environment : Environment code) : Preserves code Kind.sat_word.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_sat_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_add (code) (environment : Environment code) : Preserves code Kind.u256_add.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_add, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.primitive code _ _ _
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.declared
      apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.primitive code _ _ _
      · apply Input.LocalEffects.declared
        apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.primitive code _ _ _
        · exact Input.LocalEffects.returned code _

theorem pure_u256_add_carry (code) (environment : Environment code) : Preserves code Kind.u256_add_carry.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_add_carry, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.primitive code _ _ _
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.declared
      apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.primitive code _ _ _
      · apply Input.LocalEffects.declared
        apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.primitive code _ _ _
        · exact Input.LocalEffects.returned code _

theorem pure_u256_and (code) (environment : Environment code) : Preserves code Kind.u256_and.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_and, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_eq (code) (environment : Environment code) : Preserves code Kind.u256_eq.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_eq, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_fits_word (code) (environment : Environment code) : Preserves code Kind.u256_fits_word.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_fits_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_from_word (code) (environment : Environment code) : Preserves code Kind.u256_from_word.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_from_word, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_is_zero (code) (environment : Environment code) : Preserves code Kind.u256_is_zero.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_is_zero, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_limb (code) (environment : Environment code) : Preserves code Kind.u256_limb.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_limb, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _

theorem pure_u256_low (code) (environment : Environment code) : Preserves code Kind.u256_low.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_low, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_lt (code) (environment : Environment code) : Preserves code Kind.u256_lt.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_lt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · exact Input.LocalEffects.returned code _
            · exact Input.LocalEffects.skip code
          · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _

theorem pure_u256_neg (code) (environment : Environment code) : Preserves code Kind.u256_neg.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_neg, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.primitive code _ _ _
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.declared
      apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.primitive code _ _ _
      · apply Input.LocalEffects.declared
        apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.primitive code _ _ _
        · exact Input.LocalEffects.returned code _

theorem pure_u256_not (code) (environment : Environment code) : Preserves code Kind.u256_not.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_not, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_or (code) (environment : Environment code) : Preserves code Kind.u256_or.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_or, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_shl (code) (environment : Environment code) : Preserves code Kind.u256_shl.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_shl, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.skip code
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · apply Input.LocalEffects.sequence
                  · exact Input.LocalEffects.assign code _ _
                  · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.skip code
          · exact Input.LocalEffects.returned code _

theorem pure_u256_shr (code) (environment : Environment code) : Preserves code Kind.u256_shr.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_shr, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.assign code _ _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.skip code
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · apply Input.LocalEffects.sequence
                  · exact Input.LocalEffects.assign code _ _
                  · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.skip code
          · exact Input.LocalEffects.returned code _

theorem pure_u256_slt (code) (environment : Environment code) : Preserves code Kind.u256_slt.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_slt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · exact Input.LocalEffects.returned code _
            · exact Input.LocalEffects.skip code
          · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.returned code _
          · exact Input.LocalEffects.skip code
        · exact Input.LocalEffects.returned code _

theorem pure_u256_sub (code) (environment : Environment code) : Preserves code Kind.u256_sub.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sub, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.primitive code _ _ _
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.declared
      apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.primitive code _ _ _
      · apply Input.LocalEffects.declared
        apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.primitive code _ _ _
        · exact Input.LocalEffects.returned code _

theorem pure_u256_xor (code) (environment : Environment code) : Preserves code Kind.u256_xor.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_xor, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.returned code _

theorem pure_u256_abs (code) (environment : Environment code) : Preserves code Kind.u256_abs.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_abs, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.call_body code none (ofString "u256_neg") _ _ _ _ (environment .u256_neg) (pure_u256_neg code environment)
    · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_bit (code) (environment : Environment code) : Preserves code Kind.u256_bit.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_bit, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_limb") _ _ _ _ _ (environment .u256_limb) (pure_u256_limb code environment) ?_
    exact Input.LocalEffects.returned code _

theorem pure_u256_bit_length (code) (environment : Environment code) : Preserves code Kind.u256_bit_length.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_bit_length, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · refine Input.LocalEffects.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ (environment .bit_length64) (pure_bit_length64 code environment) ?_
      exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · refine Input.LocalEffects.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ (environment .bit_length64) (pure_bit_length64 code environment) ?_
        exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · refine Input.LocalEffects.scoped_body code _ _ (ofString "bit_length64") _ _ _ _ _ (environment .bit_length64) (pure_bit_length64 code environment) ?_
          exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · exact Input.LocalEffects.call_body code none (ofString "bit_length64") _ _ _ _ (environment .bit_length64) (pure_bit_length64 code environment)

theorem pure_u256_byte (code) (environment : Environment code) : Preserves code Kind.u256_byte.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_byte, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.declared
    refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_limb") _ _ _ _ _ (environment .u256_limb) (pure_u256_limb code environment) ?_
    exact Input.LocalEffects.returned code _

theorem pure_u256_cmp (code) (environment : Environment code) : Preserves code Kind.u256_cmp.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_cmp, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_lt") _ _ _ _ _ (environment .u256_lt) (pure_u256_lt code environment) ?_
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_eq") _ _ _ _ _ (environment .u256_eq) (pure_u256_eq code environment) ?_
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.returned code _
      · exact Input.LocalEffects.skip code
    · exact Input.LocalEffects.returned code _

theorem pure_u256_from_be (code) (environment : Environment code) : Preserves code Kind.u256_from_be.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_from_be, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.declared
      refine Input.LocalEffects.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ (environment .bswap64) (pure_bswap64 code environment) ?_
      apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · refine Input.LocalEffects.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ (environment .bswap64) (pure_bswap64 code environment) ?_
        apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · refine Input.LocalEffects.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ (environment .bswap64) (pure_bswap64 code environment) ?_
          apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · refine Input.LocalEffects.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ (environment .bswap64) (pure_bswap64 code environment) ?_
            exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.loop
      apply Input.LocalEffects.declared
      apply Input.LocalEffects.declared
      apply Input.LocalEffects.declared
      apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.assign code _ _
        · exact Input.LocalEffects.skip code
      · apply Input.LocalEffects.sequence
        · apply Input.LocalEffects.conditional
          · exact Input.LocalEffects.assign code _ _
          · exact Input.LocalEffects.skip code
        · apply Input.LocalEffects.sequence
          · apply Input.LocalEffects.conditional
            · exact Input.LocalEffects.assign code _ _
            · exact Input.LocalEffects.skip code
          · apply Input.LocalEffects.sequence
            · apply Input.LocalEffects.conditional
              · exact Input.LocalEffects.assign code _ _
              · exact Input.LocalEffects.skip code
            · exact Input.LocalEffects.assign code _ _
    · exact Input.LocalEffects.returned code _

theorem pure_u256_gt (code) (environment : Environment code) : Preserves code Kind.u256_gt.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_gt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.call_body code none (ofString "u256_lt") _ _ _ _ (environment .u256_lt) (pure_u256_lt code environment)

theorem pure_u256_mul (code) (environment : Environment code) : Preserves code Kind.u256_mul.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_mul, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
      exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.declared
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.assign code _ _
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.primitive code _ _ _
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.assign code _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.primitive code _ _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · apply Input.LocalEffects.declared
                  apply Input.LocalEffects.sequence
                  · exact Input.LocalEffects.assign code _ _
                  · apply Input.LocalEffects.sequence
                    · exact Input.LocalEffects.assign code _ _
                    · apply Input.LocalEffects.sequence
                      · exact Input.LocalEffects.primitive code _ _ _
                      · apply Input.LocalEffects.sequence
                        · exact Input.LocalEffects.assign code _ _
                        · apply Input.LocalEffects.sequence
                          · exact Input.LocalEffects.assign code _ _
                          · apply Input.LocalEffects.sequence
                            · exact Input.LocalEffects.primitive code _ _ _
                            · apply Input.LocalEffects.sequence
                              · exact Input.LocalEffects.assign code _ _
                              · apply Input.LocalEffects.sequence
                                · exact Input.LocalEffects.assign code _ _
                                · apply Input.LocalEffects.sequence
                                  · exact Input.LocalEffects.primitive code _ _ _
                                  · apply Input.LocalEffects.sequence
                                    · exact Input.LocalEffects.assign code _ _
                                    · apply Input.LocalEffects.sequence
                                      · exact Input.LocalEffects.assign code _ _
                                      · apply Input.LocalEffects.sequence
                                        · exact Input.LocalEffects.primitive code _ _ _
                                        · apply Input.LocalEffects.sequence
                                          · exact Input.LocalEffects.assign code _ _
                                          · apply Input.LocalEffects.sequence
                                            · exact Input.LocalEffects.assign code _ _
                                            · apply Input.LocalEffects.sequence
                                              · exact Input.LocalEffects.primitive code _ _ _
                                              · apply Input.LocalEffects.sequence
                                                · exact Input.LocalEffects.assign code _ _
                                                · apply Input.LocalEffects.sequence
                                                  · exact Input.LocalEffects.assign code _ _
                                                  · apply Input.LocalEffects.declared
                                                    apply Input.LocalEffects.sequence
                                                    · exact Input.LocalEffects.assign code _ _
                                                    · apply Input.LocalEffects.sequence
                                                      · exact Input.LocalEffects.assign code _ _
                                                      · apply Input.LocalEffects.declared
                                                        exact Input.LocalEffects.returned code _

theorem pure_u256_mul_full (code) (environment : Environment code) : Preserves code Kind.u256_mul_full.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_mul_full, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  refine Input.LocalEffects.scoped_body code _ _ (ofString "mul64x64") _ _ _ _ _ (environment .mul64x64) (pure_mul64x64 code environment) ?_
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · exact Input.LocalEffects.assign code _ _
  · apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.primitive code _ _ _
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · apply Input.LocalEffects.sequence
        · exact Input.LocalEffects.assign code _ _
        · apply Input.LocalEffects.sequence
          · exact Input.LocalEffects.primitive code _ _ _
          · apply Input.LocalEffects.sequence
            · exact Input.LocalEffects.assign code _ _
            · apply Input.LocalEffects.sequence
              · exact Input.LocalEffects.assign code _ _
              · apply Input.LocalEffects.declared
                apply Input.LocalEffects.sequence
                · exact Input.LocalEffects.assign code _ _
                · apply Input.LocalEffects.sequence
                  · exact Input.LocalEffects.assign code _ _
                  · apply Input.LocalEffects.sequence
                    · exact Input.LocalEffects.primitive code _ _ _
                    · apply Input.LocalEffects.sequence
                      · exact Input.LocalEffects.assign code _ _
                      · apply Input.LocalEffects.sequence
                        · exact Input.LocalEffects.assign code _ _
                        · apply Input.LocalEffects.sequence
                          · exact Input.LocalEffects.primitive code _ _ _
                          · apply Input.LocalEffects.sequence
                            · exact Input.LocalEffects.assign code _ _
                            · apply Input.LocalEffects.sequence
                              · exact Input.LocalEffects.assign code _ _
                              · apply Input.LocalEffects.sequence
                                · exact Input.LocalEffects.primitive code _ _ _
                                · apply Input.LocalEffects.sequence
                                  · exact Input.LocalEffects.assign code _ _
                                  · apply Input.LocalEffects.sequence
                                    · exact Input.LocalEffects.assign code _ _
                                    · apply Input.LocalEffects.sequence
                                      · exact Input.LocalEffects.primitive code _ _ _
                                      · apply Input.LocalEffects.sequence
                                        · exact Input.LocalEffects.assign code _ _
                                        · apply Input.LocalEffects.sequence
                                          · exact Input.LocalEffects.assign code _ _
                                          · apply Input.LocalEffects.sequence
                                            · exact Input.LocalEffects.primitive code _ _ _
                                            · apply Input.LocalEffects.sequence
                                              · exact Input.LocalEffects.assign code _ _
                                              · apply Input.LocalEffects.sequence
                                                · exact Input.LocalEffects.assign code _ _
                                                · apply Input.LocalEffects.declared
                                                  apply Input.LocalEffects.sequence
                                                  · exact Input.LocalEffects.assign code _ _
                                                  · apply Input.LocalEffects.sequence
                                                    · exact Input.LocalEffects.assign code _ _
                                                    · apply Input.LocalEffects.sequence
                                                      · exact Input.LocalEffects.primitive code _ _ _
                                                      · apply Input.LocalEffects.sequence
                                                        · exact Input.LocalEffects.assign code _ _
                                                        · apply Input.LocalEffects.sequence
                                                          · exact Input.LocalEffects.assign code _ _
                                                          · apply Input.LocalEffects.sequence
                                                            · exact Input.LocalEffects.primitive code _ _ _
                                                            · apply Input.LocalEffects.sequence
                                                              · exact Input.LocalEffects.assign code _ _
                                                              · apply Input.LocalEffects.sequence
                                                                · exact Input.LocalEffects.assign code _ _
                                                                · apply Input.LocalEffects.sequence
                                                                  · exact Input.LocalEffects.primitive code _ _ _
                                                                  · apply Input.LocalEffects.sequence
                                                                    · exact Input.LocalEffects.assign code _ _
                                                                    · apply Input.LocalEffects.sequence
                                                                      · exact Input.LocalEffects.assign code _ _
                                                                      · apply Input.LocalEffects.sequence
                                                                        · exact Input.LocalEffects.primitive code _ _ _
                                                                        · apply Input.LocalEffects.sequence
                                                                          · exact Input.LocalEffects.assign code _ _
                                                                          · apply Input.LocalEffects.sequence
                                                                            · exact Input.LocalEffects.assign code _ _
                                                                            · apply Input.LocalEffects.sequence
                                                                              · exact Input.LocalEffects.primitive code _ _ _
                                                                              · apply Input.LocalEffects.sequence
                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                · apply Input.LocalEffects.sequence
                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                  · apply Input.LocalEffects.sequence
                                                                                    · exact Input.LocalEffects.primitive code _ _ _
                                                                                    · apply Input.LocalEffects.sequence
                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                      · apply Input.LocalEffects.sequence
                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                        · apply Input.LocalEffects.sequence
                                                                                          · exact Input.LocalEffects.primitive code _ _ _
                                                                                          · apply Input.LocalEffects.sequence
                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                            · apply Input.LocalEffects.sequence
                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                              · apply Input.LocalEffects.declared
                                                                                                apply Input.LocalEffects.sequence
                                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                                · apply Input.LocalEffects.sequence
                                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                    · exact Input.LocalEffects.primitive code _ _ _
                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                          · exact Input.LocalEffects.primitive code _ _ _
                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                                            · apply Input.LocalEffects.sequence
                                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                                              · apply Input.LocalEffects.sequence
                                                                                                                · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                    · exact Input.LocalEffects.assign code _ _
                                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                                      · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                                          · exact Input.LocalEffects.assign code _ _
                                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                                            · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                            · apply Input.LocalEffects.sequence
                                                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                                                              · apply Input.LocalEffects.sequence
                                                                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                                  · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                                    · exact Input.LocalEffects.assign code _ _
                                                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                                        · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                                                          · exact Input.LocalEffects.assign code _ _
                                                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                                                                            · apply Input.LocalEffects.declared
                                                                                                                                              apply Input.LocalEffects.sequence
                                                                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                                                                              · apply Input.LocalEffects.sequence
                                                                                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                                                  · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                                                    · exact Input.LocalEffects.assign code _ _
                                                                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                                                        · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                                                                          · exact Input.LocalEffects.assign code _ _
                                                                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                                                                                            · apply Input.LocalEffects.sequence
                                                                                                                                                              · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                              · apply Input.LocalEffects.sequence
                                                                                                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                                                                    · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                                                                                          · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                            · apply Input.LocalEffects.sequence
                                                                                                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                              · apply Input.LocalEffects.declared
                                                                                                                                                                                apply Input.LocalEffects.sequence
                                                                                                                                                                                · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                                                                                    · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                                                    · apply Input.LocalEffects.sequence
                                                                                                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                        · apply Input.LocalEffects.sequence
                                                                                                                                                                                          · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                                                          · apply Input.LocalEffects.sequence
                                                                                                                                                                                            · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                            · apply Input.LocalEffects.sequence
                                                                                                                                                                                              · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                              · apply Input.LocalEffects.sequence
                                                                                                                                                                                                · exact Input.LocalEffects.primitive code _ _ _
                                                                                                                                                                                                · apply Input.LocalEffects.sequence
                                                                                                                                                                                                  · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                                  · apply Input.LocalEffects.sequence
                                                                                                                                                                                                    · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                                    · apply Input.LocalEffects.declared
                                                                                                                                                                                                      apply Input.LocalEffects.sequence
                                                                                                                                                                                                      · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                                      · apply Input.LocalEffects.sequence
                                                                                                                                                                                                        · exact Input.LocalEffects.assign code _ _
                                                                                                                                                                                                        · apply Input.LocalEffects.declared
                                                                                                                                                                                                          exact Input.LocalEffects.returned code _

theorem pure_u256_sar (code) (environment : Environment code) : Preserves code Kind.u256_sar.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sar, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · apply Input.LocalEffects.sequence
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.returned code _
        · exact Input.LocalEffects.skip code
      · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_shr") _ _ _ _ _ (environment .u256_shr) (pure_u256_shr code environment) ?_
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · apply Input.LocalEffects.conditional
        · refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_shl") _ _ _ _ _ (environment .u256_shl) (pure_u256_shl code environment) ?_
          exact Input.LocalEffects.call_body code (some (some _)) (ofString "u256_or") _ _ _ _ (environment .u256_or) (pure_u256_or code environment)
        · exact Input.LocalEffects.skip code
      · exact Input.LocalEffects.skip code
    · exact Input.LocalEffects.returned code _

theorem pure_u256_sgt (code) (environment : Environment code) : Preserves code Kind.u256_sgt.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_sgt, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact Input.LocalEffects.call_body code none (ofString "u256_slt") _ _ _ _ (environment .u256_slt) (pure_u256_slt code environment)

theorem pure_u256_byte_length (code) (environment : Environment code) : Preserves code Kind.u256_byte_length.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_byte_length, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_bit_length") _ _ _ _ _ (environment .u256_bit_length) (pure_u256_bit_length code environment) ?_
  exact Input.LocalEffects.returned code _

theorem pure_u256_exp (code) (environment : Environment code) : Preserves code Kind.u256_exp.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_exp, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_bit_length") _ _ _ _ _ (environment .u256_bit_length) (pure_u256_bit_length code environment) ?_
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.loop
    refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_bit") _ _ _ _ _ (environment .u256_bit) (pure_u256_bit code environment) ?_
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.call_body code (some (some _)) (ofString "u256_mul") _ _ _ _ (environment .u256_mul) (pure_u256_mul code environment)
      · exact Input.LocalEffects.skip code
    · apply Input.LocalEffects.sequence
      · exact Input.LocalEffects.assign code _ _
      · apply Input.LocalEffects.conditional
        · exact Input.LocalEffects.call_body code (some (some _)) (ofString "u256_mul") _ _ _ _ (environment .u256_mul) (pure_u256_mul code environment)
        · exact Input.LocalEffects.skip code
  · exact Input.LocalEffects.returned code _

theorem pure_u256_signextend (code) (environment : Environment code) : Preserves code Kind.u256_signextend.body := by
  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_u256_signextend, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.conditional
    · exact Input.LocalEffects.returned code _
    · exact Input.LocalEffects.skip code
  · apply Input.LocalEffects.declared
    refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_bit") _ _ _ _ _ (environment .u256_bit) (pure_u256_bit code environment) ?_
    refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_shl") _ _ _ _ _ (environment .u256_shl) (pure_u256_shl code environment) ?_
    apply Input.LocalEffects.sequence
    · apply Input.LocalEffects.conditional
      · exact Input.LocalEffects.call_body code none (ofString "u256_or") _ _ _ _ (environment .u256_or) (pure_u256_or code environment)
      · exact Input.LocalEffects.skip code
    · refine Input.LocalEffects.scoped_body code _ _ (ofString "u256_not") _ _ _ _ _ (environment .u256_not) (pure_u256_not code environment) ?_
      exact Input.LocalEffects.call_body code none (ofString "u256_and") _ _ _ _ (environment .u256_and) (pure_u256_and code environment)

theorem original_preserves (kind : Kind) (code) (environment : Environment code) : Preserves code kind.body := by
  cases kind with
  | add_sat => exact pure_add_sat code environment
  | bit_length64 => exact pure_bit_length64 code environment
  | bswap64 => exact pure_bswap64 code environment
  | ceil_log2 => exact pure_ceil_log2 code environment
  | digits_len => exact pure_digits_len code environment
  | digits_to_u256 => exact pure_digits_to_u256 code environment
  | div64by32 => exact pure_div64by32 code environment
  | max => exact pure_max code environment
  | min => exact pure_min code environment
  | mul64x64 => exact pure_mul64x64 code environment
  | nlz32 => exact pure_nlz32 code environment
  | sat_word => exact pure_sat_word code environment
  | u256_add => exact pure_u256_add code environment
  | u256_add_carry => exact pure_u256_add_carry code environment
  | u256_and => exact pure_u256_and code environment
  | u256_eq => exact pure_u256_eq code environment
  | u256_fits_word => exact pure_u256_fits_word code environment
  | u256_from_word => exact pure_u256_from_word code environment
  | u256_is_zero => exact pure_u256_is_zero code environment
  | u256_limb => exact pure_u256_limb code environment
  | u256_low => exact pure_u256_low code environment
  | u256_lt => exact pure_u256_lt code environment
  | u256_neg => exact pure_u256_neg code environment
  | u256_not => exact pure_u256_not code environment
  | u256_or => exact pure_u256_or code environment
  | u256_shl => exact pure_u256_shl code environment
  | u256_shr => exact pure_u256_shr code environment
  | u256_slt => exact pure_u256_slt code environment
  | u256_sub => exact pure_u256_sub code environment
  | u256_xor => exact pure_u256_xor code environment
  | u256_abs => exact pure_u256_abs code environment
  | u256_bit => exact pure_u256_bit code environment
  | u256_bit_length => exact pure_u256_bit_length code environment
  | u256_byte => exact pure_u256_byte code environment
  | u256_cmp => exact pure_u256_cmp code environment
  | u256_from_be => exact pure_u256_from_be code environment
  | u256_gt => exact pure_u256_gt code environment
  | u256_mul => exact pure_u256_mul code environment
  | u256_mul_full => exact pure_u256_mul_full code environment
  | u256_sar => exact pure_u256_sar code environment
  | u256_sgt => exact pure_u256_sgt code environment
  | u256_byte_length => exact pure_u256_byte_length code environment
  | u256_exp => exact pure_u256_exp code environment
  | u256_signextend => exact pure_u256_signextend code environment

/-- Every checked arithmetic helper retains all nonlocal fields at
every clock and for every outcome. No input-shape or callee-success premise. -/
theorem execution_frame (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment source.code) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source kind.body = (result, target)) :
    erase target = erase source := by
  have pureBody := original_preserves kind source.code environment
  unfold Input.LocalEffects.Preserves at pureBody
  have frame := pureBody source rfl
  simpa only [run] using frame

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.original_preserves
#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.execution_frame
