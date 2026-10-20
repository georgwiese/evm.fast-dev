import InitECandidate.Solver.Input.RequestOffsetsProgram
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem offsets_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) (clock : Nat) :
    InitializerAllocations.context {offsetsStored source input array with clock := clock} = InitializerAllocations.context source := rfl

theorem offsets_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :
    (offsetsStored source input array).globals = source.globals := rfl

theorem offsets_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) (key : String)
    (rq : ofString "o_rq" ≠ ofString key) (vh : ofString "o_vh" ≠ ofString key) (pl : ofString "o_pl" ≠ ofString key) :
    (offsetsStored source input array).locals.lookup (ofString key) = source.locals.lookup (ofString key) :=
  (bind_lookup_other (offsetSecond source input) "o_rq" _ _ rq).trans
    ((bind_lookup_other (offsetFirst source input) "o_vh" _ _ vh).trans
      (bind_lookup_other source "o_pl" _ _ pl))

theorem offsets_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array : BitVec 64) :
    (offsetsStored source input array).locals.lookup (ofString "o_pl") = some (.val (.word (requestWords input 0))) ∧
    (offsetsStored source input array).locals.lookup (ofString "o_vh") = some (.val (.word (requestWords input 1))) ∧
    (offsetsStored source input array).locals.lookup (ofString "o_rq") = some (.val (.word (requestWords input 2))) := by
  refine ⟨?_,?_,?_⟩
  · exact (bind_lookup_other (offsetSecond source input) "o_rq" "o_pl" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "o_pl" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other (offsetSecond source input) "o_rq" "o_vh" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

theorem restore_offsets_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    emptyLocalsHOLFinite (restoreOffsets source input target) = emptyLocalsHOLFinite target := rfl

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offsets_context
#print axioms InitECandidate.Solver.Input.Request.offsets_globals
#print axioms InitECandidate.Solver.Input.Request.offsets_other
#print axioms InitECandidate.Solver.Input.Request.offsets_bindings

#print axioms InitECandidate.Solver.Input.Request.restore_offsets_frame
