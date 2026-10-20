import InitECandidate.Solver.Input.MainBlsConstantsProgram
import InitECandidate.Solver.Input.WordTableFields

namespace InitECandidate.Solver.Input.Main.BlsConstants
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := WordTableInitialization.template source cursor action words

/-- The real first-time constant initializer performs its allocation and all
892 actual stores, spending exactly one body tick. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 7136 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 1}) := by
  rw [body_shape]
  exact WordTableInitialization.execute source cursor action words installed scalars heap zero valid domain lower room aligned
    (by rw [words_length]; rfl) enough

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 7136 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,{template source cursor with clock := source.clock - 2}) := by
  have code := original_code source.code installed
  rw [body_shape] at code
  exact WordTableInitialization.call_execute source cursor action words (ofString "bls_consts_init") code installed scalars heap zero valid domain lower room aligned
    (by rw [words_length]; rfl) enough

/-- The three later setup helpers really call the same initialized function. -/
theorem initialized_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word pointer))) (nonzero : pointer ≠ 0#64) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bls_consts_init") []) = (none,{source with clock := source.clock - 1}) := by
  have code := original_code source.code installed
  rw [body_shape] at code
  exact WordTableInitialization.initialized_call source action words (ofString "bls_consts_init") pointer code binding nonzero enough

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := WordTableInitialization.template_context source cursor action words

theorem template_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).globals.lookup (ofString "bls_c") = some (.val (.word (BitVec.ofNat 64 cursor))) := WordTableInitialization.template_binding source cursor action words

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := WordTableInitialization.template_scalars source cursor action words scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7136)))) := WordTableInitialization.template_heap source cursor action words heap valid

end InitECandidate.Solver.Input.Main.BlsConstants

#print axioms InitECandidate.Solver.Input.Main.BlsConstants.execute
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.call_execute
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.initialized_call
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.template_context
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.template_binding
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsConstants.template_heap
