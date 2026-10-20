import InitECandidate.Solver.Input.MainBlsProgram
import InitECandidate.Solver.Input.MainBlsBufferFields

namespace InitECandidate.Solver.Input.Main.BlsPairInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_other_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (params : key ≠ ofString (paramsName kind))
    (first : key ≠ ofString (firstName kind)) (second : key ≠ ofString (secondName kind)) :
    (template source cursor kind).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocationAliases.step_other source cursor (block kind) key heap params
  intro action member
  simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact first
  · exact second

end InitECandidate.Solver.Input.Main.BlsPairInitialization

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def constantsTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := BlsConstants.template source cursor
def fpTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := BlsFpInitialization.template (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor)
def fp2Template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := BlsPairInitialization.template (fpTemplate source cursor) (cursor + 7376) .fp2
def libTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := BlsPairInitialization.template (fp2Template source cursor) (cursor + 7568) .g1

theorem constants_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    constantsTemplate {source with clock := clock} cursor = {constantsTemplate source cursor with clock := clock} := WordTableInitialization.template_clock source cursor BlsConstants.action BlsConstants.words clock

theorem fp_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    fpTemplate {source with clock := clock} cursor = {fpTemplate source cursor with clock := clock} := by
  unfold fpTemplate
  rw [constants_clock source cursor clock]
  exact BlsFpInitialization.template_clock (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) clock

theorem fp2_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    fp2Template {source with clock := clock} cursor = {fp2Template source cursor with clock := clock} := by
  unfold fp2Template
  rw [fp_clock source cursor clock]
  exact BlsPairInitialization.template_clock (fpTemplate source cursor) (cursor + 7376) .fp2 clock

theorem lib_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    libTemplate {source with clock := clock} cursor = {libTemplate source cursor with clock := clock} := by
  unfold libTemplate
  rw [fp2_clock source cursor clock]
  exact BlsPairInitialization.template_clock (fp2Template source cursor) (cursor + 7568) .g1 clock

theorem constants_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (constantsTemplate source cursor) = InitializerAllocations.context source := BlsConstants.template_context source cursor

theorem fp_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (fpTemplate source cursor) = InitializerAllocations.context source :=
  (BlsFpInitialization.template_context (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor)).trans (constants_context source cursor)

theorem fp2_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (fp2Template source cursor) = InitializerAllocations.context source :=
  (BlsPairInitialization.template_context (fpTemplate source cursor) (cursor + 7376) .fp2).trans (fp_context source cursor)

theorem lib_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (libTemplate source cursor) = InitializerAllocations.context source :=
  (BlsPairInitialization.template_context (fp2Template source cursor) (cursor + 7568) .g1).trans (fp2_context source cursor)

theorem constants_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (constantsTemplate source cursor).globals := BlsConstants.template_scalars source cursor scalars

theorem fp_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (fpTemplate source cursor).globals := BlsFpInitialization.template_scalars (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) (constants_scalars source cursor scalars)

theorem fp2_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (fp2Template source cursor).globals := BlsPairInitialization.template_scalars (fpTemplate source cursor) (cursor + 7376) .fp2 (fp_scalars source cursor scalars)

theorem lib_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (libTemplate source cursor).globals := BlsPairInitialization.template_scalars (fp2Template source cursor) (cursor + 7568) .g1 (fp2_scalars source cursor scalars)

theorem constants_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (constantsTemplate source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7136)))) := BlsConstants.template_heap source cursor heap

theorem fp_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (fpTemplate source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7376)))) := by
  simpa only [fpTemplate,Nat.add_assoc,show 7136 + 240 = 7376 from rfl] using BlsFpInitialization.template_heap (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) (constants_heap source cursor heap)

theorem fp2_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (fp2Template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7568)))) := by
  simpa only [fp2Template,Nat.add_assoc,show 7376 + 192 = 7568 from rfl] using BlsPairInitialization.template_heap (fpTemplate source cursor) (cursor + 7376) .fp2 (fp_heap source cursor heap)

theorem lib_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (libTemplate source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7760)))) := by
  simpa only [libTemplate,Nat.add_assoc,show 7568 + 192 = 7760 from rfl] using BlsPairInitialization.template_heap (fp2Template source cursor) (cursor + 7568) .g1 (fp2_heap source cursor heap)

theorem constants_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (constantsTemplate source cursor).globals.lookup (ofString "bls_c") = some (.val (.word (BitVec.ofNat 64 cursor))) := BlsConstants.template_binding source cursor

theorem fp_constants (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (fpTemplate source cursor).globals.lookup (ofString "bls_c") = some (.val (.word (BitVec.ofNat 64 cursor))) :=
  (BlsFpInitialization.template_constants (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor)).trans (constants_binding source cursor)

theorem fp2_constants (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (fp2Template source cursor).globals.lookup (ofString "bls_c") = some (.val (.word (BitVec.ofNat 64 cursor))) :=
  (BlsPairInitialization.template_constants (fpTemplate source cursor) (cursor + 7376) .fp2).trans (fp_constants source cursor)

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_other_fields
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_context
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_context
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_context
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_context
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_heap
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_heap
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_heap
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_heap
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.constants_binding
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_constants
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp2_constants
