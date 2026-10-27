import InitECandidate.Solver.Input.CurrentStartup.DecoderHeap
import InitECandidate.Solver.Input.CurrentStartup.PrecheckHostFrame
import InitECandidate.Solver.Input.BlobReached

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The fixed decoder first checks the host header, then copies input and
passes the actual tuple fields to the stateless decoder by tail call. -/
def precheck : ProgHOL 64 := .call (some (none, none)) (Code.name .precheck_host_ssz_header) []

def stateless : ProgHOL 64 := .call none (Code.name .decode_stateless_input)
  [.rfield 0 (.var .local (ofString "inp")), .rfield 1 (.var .local (ofString "inp"))]

def afterPrecheck : ProgHOL 64 := .decCall (ofString "inp") Blob.returnShape (ofString "input_blob") [] stateless

theorem source_shape : Code.body .decode_host_input = .seq precheck afterPrecheck := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_decode_host_input, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none,
    precheck, afterPrecheck, stateless, Blob.returnShape, Code.name]

theorem precheck_host (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code precheck :=
  ReadHostEffects.call_body code (some none) (Code.name .precheck_host_ssz_header) []
    (Code.formals .precheck_host_ssz_header) (Code.body .precheck_host_ssz_header) (Code.shape .precheck_host_ssz_header)
    (Code.installed code installed .precheck_host_ssz_header)
    (ReadOnlyPrecheck.precheck_host_ssz_header code installed)

theorem precheck_global (selected : MlS) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves selected code precheck :=
  GlobalEffects.call_body selected code (some none) (Code.name .precheck_host_ssz_header) []
    (Code.formals .precheck_host_ssz_header) (Code.body .precheck_host_ssz_header) (Code.shape .precheck_host_ssz_header)
    (Code.installed code installed .precheck_host_ssz_header)
    (PrecheckHostSszHeader.any_key selected code installed)

/-- Every actual precheck outcome retains input host bytes and both arena
cursors, byte order, oracle, installed code/domain and the current heap cell.
Its output memory/event history may change; no precheck success is assumed. -/
theorem precheck_state (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source) (heap : HeapState source)
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source precheck = (result, target)) :
    HostState input target ∧ HeapState target := by
  have host := precheck_host source.code initial.arena.code source rfl initial.oracle
  have scratch := precheck_global (key .scratch) source.code initial.arena.code source rfl
  have frame := precheck_global (key .frame) source.code initial.arena.code source rfl
  have cursor := precheck_global (ofString "heap_ptr") source.code initial.arena.code source rfl
  rw [actual] at host scratch frame cursor
  have fields := evaluation_fields source target precheck result actual
  have layout := evaluation_layout source target precheck result actual
  have shapes : OriginalExceptions.Installed target.eshapes := by rw [fields.2.2.1]; exact initial.shapes
  have code : OriginalCode.Installed target.code := by rw [fields.2.2.2]; exact initial.arena.code
  have arena : ArenaState target := ⟨(congrArg Prod.snd scratch).trans initial.arena.scratch,
    (congrArg Prod.snd frame).trans initial.arena.frame, fields.1.trans initial.arena.domain, code⟩
  obtain ⟨pointer, heapCell, bound, aligned⟩ := heap
  exact ⟨⟨arena, fields.2.1.trans initial.little,
    (evaluation_oracle source target precheck result actual).trans initial.oracle, host.trans initial.host,
    shapes, layout.1.trans initial.shared, layout.2.trans initial.base⟩,
    pointer, (congrArg Prod.snd cursor).trans heapCell, bound, aligned⟩

/-- A real returning decoder body passes its actual precheck and input_blob
call. The copied byte image, encoded-length bound and live inp tuple are
therefore derived at the genuine stateless tail-call continuation. -/
theorem body_copied (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source) (heap : HeapState source) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_host_input) = (some (.returned value), target)) :
    ∃ before pointer ready inner,
      evaluateHOLFiniteState source precheck = (none, before) ∧
      HostState input before ∧
      before.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      pointer.toNat ≤ 2952790016 ∧ pointer.toNat % 8 = 0 ∧
      input.length % 2^64 ≤ Guest.maxInputBytes ∧
      ready.locals.lookup (ofString "inp") = some (.rStruct [.val (.word pointer),
        .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]) ∧
      Blob.Copied {before with clock := before.clock - 1} ready input pointer (input.length % 2^64)
        (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]) ∧
      evaluateHOLFiniteState ready stateless = (some (.returned value), inner) ∧
      target = WitnessRadix.QueryBranch.restore before "inp" inner ∧
      CallPrefix.Reaches before (.scoped (ofString "inp") Blob.returnShape (ofString "input_blob") []) ready := by
  have safe : LocalPrefix (ofString "inp") precheck :=
    .call none _ _ (by intro name impossible; cases impossible)
  rw [source_shape] at actual
  obtain ⟨before, precheckRun, suffix, saved⟩ := safe.normal_continue source target afterPrecheck value actual
  obtain ⟨readyState, pointer, heapCell, bound, aligned⟩ := precheck_state input source before initial heap none precheckRun
  obtain ⟨lengthBound, ready, inner, binding, copied, tailRun, restored, scope⟩ :=
    Blob.call_reached before target input pointer "inp" stateless value bound aligned readyState.little
      readyState.arena.code heapCell readyState.oracle readyState.host suffix
  exact ⟨before, pointer, ready, inner, precheckRun, readyState, heapCell, bound, aligned,
    lengthBound, binding, copied, tailRun, restored, scope⟩

end InitECandidate.Solver.Input.CurrentStartup.DecoderInput

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.source_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.precheck_host
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.precheck_global
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.precheck_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.body_copied
