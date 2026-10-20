import InitECandidate.Solver.Input.MainBlsLayout

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem constants_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : key ≠ ofString "bls_c") :
    (constantsTemplate source cursor).globals.lookup key = source.globals.lookup key := by
  simpa only [constantsTemplate,BlsConstants.template] using WordTableInitialization.template_other source cursor BlsConstants.action BlsConstants.words key heap other

private theorem fp_symbols_away (name : String) (member : name ∈ ["fp2_accel_params","bls_g1_accel_params","bls_discount"]) :
    ∀ changed ∈ BlsFpInitialization.symbols,ofString name ≠ ofString changed := by
  intro changed touched
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  simp only [BlsFpInitialization.symbols,List.mem_cons,List.not_mem_nil,or_false] at touched
  rcases member with rfl | rfl | rfl
  all_goals rcases touched with rfl | rfl | rfl | rfl | rfl <;> decide

theorem fp_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (zero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64))) :
    (constantsTemplate source cursor).globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)) :=
  (constants_other source cursor (ofString "fp_accel_params") (by decide) (by decide)).trans zero

theorem fp2_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64))) :
    (fpTemplate source cursor).globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)) :=
  (BlsFpInitialization.template_other (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) (ofString "fp2_accel_params") (by decide)
    (fp_symbols_away "fp2_accel_params" (by simp))).trans
      ((constants_other source cursor (ofString "fp2_accel_params") (by decide) (by decide)).trans zero)

theorem g1_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64))) :
    (fp2Template source cursor).globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)) :=
  (BlsPairInitialization.template_other_fields (fpTemplate source cursor) (cursor + 7376) .fp2 (ofString "bls_g1_accel_params") (by decide) (by decide) (by decide) (by decide)).trans
    ((BlsFpInitialization.template_other (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) (ofString "bls_g1_accel_params") (by decide)
      (fp_symbols_away "bls_g1_accel_params" (by simp))).trans
        ((constants_other source cursor (ofString "bls_g1_accel_params") (by decide) (by decide)).trans zero))

theorem lib_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (constants : key ≠ ofString "bls_c")
    (fp : ∀ name ∈ BlsFpInitialization.symbols,key ≠ ofString name) (pairs : ∀ name ∈ BlsPairInitialization.symbols,key ≠ ofString name) :
    (libTemplate source cursor).globals.lookup key = source.globals.lookup key :=
  (BlsPairInitialization.template_other (fp2Template source cursor) (cursor + 7568) .g1 key heap pairs).trans
    ((BlsPairInitialization.template_other (fpTemplate source cursor) (cursor + 7376) .fp2 key heap pairs).trans
      ((BlsFpInitialization.template_other (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) key heap fp).trans
        (constants_other source cursor key heap constants)))

theorem discount_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (zero : source.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64))) :
    (libTemplate source cursor).globals.lookup (ofString "bls_discount") = some (.val (.word 0#64)) := by
  rw [lib_other source cursor (ofString "bls_discount") (by decide) (by decide) (fp_symbols_away "bls_discount" (by simp))]
  · exact zero
  · intro name member
    simp only [BlsPairInitialization.symbols,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_other
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_zero
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_zero
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.g1_zero
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_other
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.discount_zero
