import InitECandidate.Solver.CurrentKeccak.Cost
import InitECandidate.Solver.Input.GlobalEffectsCall
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.CurrentKeccak
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem permutation_globals (key : MlS) (code) : GlobalEffects.Preserves key code Permutation.body := by
  simp only [Permutation.body,Guest.Software.guestFn_keccak_f1600,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _

theorem absorb_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code Absorb.body := by
  rw [Absorb.body_shape]
  apply GlobalEffects.declared
  apply GlobalEffects.sequence
  · apply GlobalEffects.conditional
    all_goals
      apply GlobalEffects.loop
      apply GlobalEffects.sequence
      · exact GlobalEffects.store key code _ _
      · exact GlobalEffects.assign key code _ _
  · apply GlobalEffects.sequence
    · exact GlobalEffects.call_body key code (some none) _ _ Permutation.formals Permutation.body .one
        (Permutation.original_code code installed) (permutation_globals key code)
    · exact GlobalEffects.returned key code _

private theorem zero_globals (key : MlS) (code) : GlobalEffects.Preserves key code Zero.body := by
  simp only [Zero.body,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.byte_store key code _ _
    | exact GlobalEffects.returned key code _

private theorem copy_globals (key : MlS) (code) : GlobalEffects.Preserves key code Copy32.body := by
  simp only [Copy32.body,Guest.Software.guestFn_memcpy,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.byte_store key code _ _
    | exact GlobalEffects.returned key code _

/-- Actual software hashing preserves every global, including heap and all
workspace pointers, on every outcome. There are no oracle-body assumptions. -/
theorem hash_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code Hash.body := by
  simp only [Hash.body,Guest.Software.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | exact GlobalEffects.skip key code
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.byte_store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (zero_globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one
        (CopyGeneral.original_code code installed) (copy_globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "keccak_absorb_block") _ Absorb.formals Absorb.body .one
        (Absorb.original_code code installed) (absorb_globals key code installed)

end InitECandidate.Solver.CurrentKeccak

#print axioms InitECandidate.Solver.CurrentKeccak.permutation_globals
#print axioms InitECandidate.Solver.CurrentKeccak.absorb_globals
#print axioms InitECandidate.Solver.CurrentKeccak.hash_globals
