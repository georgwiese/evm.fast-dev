import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.WitnessRadix.Keccak256Entry
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.GasBudget.McopyCopyProgram

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem store_byte (key : MlS) (code) (address value : ExpHOL 64) :
    Preserves key code (.storeByte address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

end InitECandidate.Solver.Input.GlobalEffects

namespace InitECandidate.Solver.WitnessRadix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Buffer routines write ordinary memory, while preserving every global
on all outcomes. This is a physical effect fact, not a runtime bound. -/
theorem Zero.globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Zero.body := by
  simp only [Zero.body,Guest.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.store_byte key code _ _
    | exact Input.GlobalEffects.returned key code _

theorem Copy32.globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Copy32.body := by
  simp only [Copy32.body,Guest.guestFn_memcpy,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.store_byte key code _ _
    | exact Input.GlobalEffects.returned key code _

theorem Keccak.globals (key : MlS) (code) : Input.GlobalEffects.Preserves key code Keccak.f1600Body := by
  simp only [Keccak.f1600Body,Guest.guestFn_keccak_f1600,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  exact Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.external key code _ _ _ _ _)
    (Input.GlobalEffects.returned key code _)

theorem KeccakAbsorb.globals (key : MlS) (code)
    (perm : code.lookup (ofString "keccak_f1600")=some (Keccak.formals,Keccak.f1600Body,.one)) :
    Input.GlobalEffects.Preserves key code KeccakAbsorb.body := by
  simp only [KeccakAbsorb.body,Guest.guestFn_keccak_absorb_block,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "keccak_f1600") _ Keccak.formals Keccak.f1600Body .one perm (Keccak.globals key code)

theorem Keccak256.globals (key : MlS) (code)
    (zero : code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (copy : code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one))
    (block : code.lookup (ofString "keccak_absorb_block")=some (KeccakAbsorb.formals,KeccakAbsorb.body,.one))
    (perm : code.lookup (ofString "keccak_f1600")=some (Keccak.formals,Keccak.f1600Body,.one)) :
    Input.GlobalEffects.Preserves key code Keccak256.body := by
  simp only [Keccak256.body,Guest.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.store_byte key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one zero (Zero.globals key code)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one copy (Copy32.globals key code)
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "keccak_absorb_block") _ KeccakAbsorb.formals KeccakAbsorb.body .one block (KeccakAbsorb.globals key code perm)

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.Input.GlobalEffects.store_byte
#print axioms InitECandidate.Solver.WitnessRadix.Zero.globals
#print axioms InitECandidate.Solver.WitnessRadix.Copy32.globals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.globals
#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.globals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.globals
