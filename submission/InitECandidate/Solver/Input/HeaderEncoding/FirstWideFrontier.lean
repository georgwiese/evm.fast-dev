import InitECandidate.Solver.Input.HeaderEncoding.FirstWideProgram
import InitECandidate.Solver.Input.RlpWrite.ByteGlobals
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixGlobals

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def beforeWideRest : List CallPrefix.Action:=beforeWideActions.drop 1

theorem before_wide_allocation : beforeWideActions=
    .scoped (ofString "buf") .one (ofString "alloc") [.const 1024#64]::beforeWideRest := rfl

theorem before_wide_rest_globals (key : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves key code (CallPrefix.program beforeWideRest .skip) := by
  simp only [beforeWideRest,beforeWideActions,firstByteFields,fieldActions,List.cons_append,List.nil_append,CallPrefix.program]
  repeat' first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | exact GlobalEffects.skip key code
    | exact GlobalEffects.assign key code _ _
    | apply GlobalEffects.scoped_body key code _ _ (ofString "rlp_encode_bytes") _ _ RlpWrite.BytesWrite.formals RlpWrite.BytesWrite.body .one
        (OriginalRlp.rlp_encode_bytes code installed) (RlpWrite.BytesWrite.globals key code installed)
    | exact GlobalEffects.call_body key code (some (some (ofString "w"))) (ofString "rlp_encode_bytes") _ RlpWrite.BytesWrite.formals RlpWrite.BytesWrite.body .one
        (OriginalRlp.rlp_encode_bytes code installed) (RlpWrite.BytesWrite.globals key code installed)

/-- A real normal encode_header passes its actual1024-byte allocation and
all seven byte fields before the first wide-value helper. The intervening
writers retain the true current heap; no output mapping is presumed. -/
theorem before_wide_frontier (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))) (bounded : buffer.toNat≤33806089496)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current inner : PanSemStateFiniteExact 64 Guest.HostMemory,buffer.toNat+1024≤33806089496 ∧ current.code=source.code ∧
      current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded buffer 1024#64))) ∧
      post.clock=inner.clock ∧ evaluateHOLFiniteState current fromWide=(some (.returned value),inner) := by
  obtain ⟨current,inner,execution,endpoint,remaining⟩:=before_wide_trace source post value normal
  rw [before_wide_allocation] at execution
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 1024#64]=some (PersistentAlloc.values 1024#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next (ofString "buf") [.const 1024#64] buffer 1024#64 beforeWideRest installed args heap bounded execution
  have unchanged:=next.globals (ofString "heap_ptr") (before_wide_rest_globals _ source.code installed)
  have cell : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded buffer 1024#64))):=by
    rw [unchanged]
    simp [PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  exact ⟨current,inner,room,next.runtime.2.2.2.1,cell,endpoint,remaining⟩

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_wide_allocation
#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_wide_rest_globals
#print axioms InitECandidate.Solver.Input.HeaderEncoding.before_wide_frontier
