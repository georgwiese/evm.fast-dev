import InitECandidate.Solver.Input.ShaCallCost
import InitECandidate.Solver.Input.BufferGlobals

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] GlobalEffects.Preserves

theorem initialize_globals (key : MlS) (code) : GlobalEffects.Preserves key code initializeBody := by
  simp only [initializeBody,Guest.guestFn_sha256_state_init,progToHOL]
  repeat first | apply GlobalEffects.sequence | exact GlobalEffects.store key code _ _ | exact GlobalEffects.returned key code _

theorem be32_globals (key : MlS) (code) : GlobalEffects.Preserves key code GasBudget.MemoryWriter.Kind.be32.body := by
  simp only [GasBudget.MemoryWriter.Kind.body,GasBudget.MemoryWriter.Kind.signature,GasBudget.MemoryWriter.Kind.original,
    Guest.guestFn_st_be32,progToHOL]
  repeat first | apply GlobalEffects.sequence | exact GlobalEffects.store_byte key code _ _ | exact GlobalEffects.returned key code _

theorem be64_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code GasBudget.MemoryWriter.Kind.be64.body := by
  have arithmetic := GasBudget.OriginalCodeEnvironment.arithmetic code installed
  have swap := GlobalEffects.of_readonly key code _ (GasBudget.ArithmeticEffects.pure_bswap64 code arithmetic)
  have swapCode := GasBudget.OriginalCodeEnvironment.arithmetic code installed .bswap64
  simp only [GasBudget.MemoryWriter.Kind.body,GasBudget.MemoryWriter.Kind.signature,GasBudget.MemoryWriter.Kind.original,
    Guest.guestFn_st_be64,progToHOL,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.conditional
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be32") _ _ _ _
        (GasBudget.MemoryWriter.original_code .be32 code installed) (be32_globals key code)
    | apply GlobalEffects.scoped_body key code _ _ (ofString "bswap64") _ _ _ _ _ swapCode swap

theorem finish_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code finishBody := by
  simp only [finishBody,Guest.guestFn_sha256_finish,progToHOL,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.declared
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be32") _ _ _ _
        (GasBudget.MemoryWriter.original_code .be32 code installed) (be32_globals key code)

theorem block_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code blockBody := by
  simp only [blockBody,Guest.guestFn_sha256_block,progToHOL,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | apply GlobalEffects.declared
    | apply GlobalEffects.conditional
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.store key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.external key code _ _ _ _ _
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ _ _ _
        (CopyGeneral.original_code code installed) (Copy32.globals key code)

def pairBody : ProgHOL 64 := match Guest.guestFn_sha256_pair with | .function fn=>progToHOL fn.body | _=>.skip
def pairFormals : List (MlS×ShapeHOL) := [(ofString "input_a",.one),(ofString "input_b",.one),(ofString "out",.one)]

set_option maxRecDepth 100000 in
theorem pair_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "sha256_pair")=some (pairFormals,pairBody,.one) := by
  have checked := OriginalCode.indexed code installed 88 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sha256_pair) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,pairFormals,pairBody,Guest.guestFn_sha256_pair,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- All original SHA helpers preserve initialized global workspace pointers,
heap cursor and every other selected global on every execution outcome. -/
theorem pair_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code pairBody := by
  simp only [pairBody,Guest.guestFn_sha256_pair,progToHOL,Option.map_none]
  repeat first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.store_byte key code _ _
    | exact GlobalEffects.returned key code _
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_state_init") _ _ _ _ (initialize_code code installed) (initialize_globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_block") _ _ _ _ (block_code code installed) (block_globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "sha256_finish") _ _ _ _ (finish_code code installed) (finish_globals key code installed)
    | exact GlobalEffects.call_body key code (some none) (ofString "memcpy") _ _ _ _ (CopyGeneral.original_code code installed) (Copy32.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "memzero") _ _ _ _ (Zero.original_code code installed) (Zero.globals key code)
    | exact GlobalEffects.call_body key code (some none) (ofString "st_be64") _ _ _ _ (GasBudget.MemoryWriter.original_code .be64 code installed) (be64_globals key code installed)

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.be32_globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.be64_globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_globals
#print axioms InitECandidate.Solver.Input.ShaFixedCost.pair_code
#print axioms InitECandidate.Solver.Input.ShaFixedCost.pair_globals
