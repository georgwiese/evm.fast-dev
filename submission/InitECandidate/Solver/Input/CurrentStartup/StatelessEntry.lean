import InitECandidate.Solver.Input.CurrentStartup.DecoderInput
import InitECandidate.Solver.Input.TailCallNormal

namespace InitECandidate.Solver.Input.CurrentStartup.DecoderInput
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Stateless

def formals : List (MlS × ShapeHOL) := [(ofString "p", .one), (ofString "len", .one)]
def values (pointer : BitVec 64) (length : Nat) : List (ValueHOL 64) :=
  [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))]
def rawLocals (pointer : BitVec 64) (length : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "len" then some (.val (.word (BitVec.ofNat 64 length)))
  else if name = ofString "p" then some (.val (.word pointer)) else none

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name .decode_stateless_input) = some (formals, Code.body .decode_stateless_input, .one) := by
  simpa only [Code.formals, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_decode_stateless_input, formals, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .decode_stateless_input

theorem environment (code) (installed : OriginalCode.Installed code) (pointer : BitVec 64) (length : Nat) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite code.lookup (Code.name .decode_stateless_input) (values pointer length) =
        some (Code.body .decode_stateless_input, callee, .one) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧
      callee.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values pointer length).length ∧
      ((formals.zip (values pointer length)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    refine ⟨by decide, rfl, ?_⟩
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact code.lookup (Code.name .decode_stateless_input) (values pointer length) =
      some (Code.body .decode_stateless_input, rawLocals pointer length, .one) := by
    simp only [lookupCodeHOLExact, original_code code installed, valid, ↓reduceIte]
    rfl
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup code.lookup _ _ _ _ .one raw
  refine ⟨callee, called, ?_, ?_⟩
  · rw [locals]; simp [rawLocals, show ofString "p" ≠ ofString "len" from by decide]
  · rw [locals]; simp [rawLocals]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (binding : source.locals.lookup (ofString "inp") = some (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))])) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [.rfield 0 (.var .local (ofString "inp")), .rfield 1 (.var .local (ofString "inp"))] = some (values pointer length) := by
  simp [values, evalListHOLFinite, evalListHOLExact, evalHOLExact, binding]

end Stateless

/-- The exact copied allocator update changes no other global cell. -/
theorem copied_global (input : Guest.InputBlob) (before ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (length : Nat) (value : ValueHOL 64)
    (copied : Blob.Copied {before with clock := before.clock - 1} ready input pointer length value)
    (selected : MlS) (other : selected ≠ ofString "heap_ptr") :
    ready.globals.lookup selected = before.globals.lookup selected := by
  rw [copied.2.2.2.2.1]
  simp [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE, Ne.symm other]

/-- The real copy trace and exact copied heap update retain entry metadata
and bootstrap the next allocation frontier. This includes byte order and
exception declarations retained by the actual lexical call action. -/
theorem copied_state (input : Guest.InputBlob) (before ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (length : Nat) (initial : HostState input before)
    (copied : Blob.Copied {before with clock := before.clock - 1} ready input pointer length
      (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))]))
    (scope : CallPrefix.Reaches before (.scoped (ofString "inp") Blob.returnShape (ofString "input_blob") []) ready) :
    HostState input ready ∧ HeapState ready := by
  obtain ⟨room, returned, bytes, clock, globals, code, domain, shared, host, oracle, memoryFrame⟩ := copied
  have readyCode : OriginalCode.Installed ready.code := by rw [scope.runtime.2.2.2.1]; exact initial.arena.code
  have arena : ArenaState ready := by
    refine ⟨?_, ?_, scope.runtime.1.trans initial.arena.domain, readyCode⟩
    · rw [globals]
      simpa [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
        key, show ofString "heap_ptr" ≠ ofString "scratch_ptr" from by decide] using initial.arena.scratch
    · rw [globals]
      simpa [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
        key, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" from by decide] using initial.arena.frame
  have shapes : OriginalExceptions.Installed ready.eshapes := by rw [scope.runtime.2.2.1]; exact initial.shapes
  have state : HostState input ready := ⟨arena, scope.runtime.2.1.trans initial.little,
    scope.runtime.2.2.2.2.trans initial.oracle, host.trans initial.host, shapes,
    scope.layout.1.trans initial.shared, scope.layout.2.trans initial.base⟩
  let amount := BitVec.ofNat 64 (length + 8)
  have amountNat : amount.toNat = length + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have guarded := WitnessRadix.PersistentAlloc.guards pointer amount (by rw [amountNat]; omega)
  refine ⟨state, WitnessRadix.PersistentAlloc.rounded pointer amount, ?_, guarded.2.2.2.1, guarded.2.2.2.2⟩
  rw [globals]
  simp [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE, amount]

/-- The actual returning host decoder reaches the real stateless decoder
with derived pointer/length parameters, byte image, current metadata and heap
frontier. Original mathematical input length is unrestricted. -/
theorem stateless_reached (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initial : HostState input source) (heap : HeapState source) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .decode_host_input) = (some (.returned value), target)) :
    ∃ before pointer ready callee post,
      input.length % 2^64 ≤ Guest.maxInputBytes ∧
      evaluateHOLFiniteState source precheck = (none, before) ∧
      Blob.Copied {before with clock := before.clock - 1} ready input pointer (input.length % 2^64)
        (.rStruct [.val (.word pointer), .val (.word (BitVec.ofNat 64 (input.length % 2^64)))]) ∧
      HostState input (callEntryStateHOLFinite ready callee) ∧
      HeapState (callEntryStateHOLFinite ready callee) ∧
      Blob.InputBytes (callEntryStateHOLFinite ready callee) input pointer (input.length % 2^64) ∧
      callee.lookup (ofString "p") = some (.val (.word pointer)) ∧
      callee.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64)))) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite ready callee) (Code.body .decode_stateless_input) =
        (some (.returned value), post) ∧
      target = WitnessRadix.QueryBranch.restore before "inp" (emptyLocalsHOLFinite post) ∧
      before.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      (∀ selected, selected ≠ ofString "heap_ptr" →
        (callEntryStateHOLFinite ready callee).globals.lookup selected = source.globals.lookup selected) := by
  obtain ⟨before, pointer, ready, inner, precheckRun, beforeState, heapCell, pointerBound, aligned,
      lengthBound, binding, copied, tailRun, restored, scope⟩ := body_copied input source target initial heap value actual
  obtain ⟨readyState, readyHeap⟩ := copied_state input before ready pointer (input.length % 2^64) beforeState copied scope
  have args := Stateless.arguments_read ready pointer (input.length % 2^64) binding
  obtain ⟨callee, called, pCell, lenCell⟩ := Stateless.environment ready.code readyState.arena.code pointer (input.length % 2^64)
  obtain ⟨positive, post, returned, checked, innerEq⟩ := CallNormal.tail_callee_return ready inner
    (Code.name .decode_stateless_input) _ _ (Code.body .decode_stateless_input) callee .one args called value tailRun
  have entry : HostState input (callEntryStateHOLFinite ready callee) :=
    ⟨⟨readyState.arena.scratch, readyState.arena.frame, readyState.arena.domain, readyState.arena.code⟩,
      readyState.little, readyState.oracle, readyState.host, readyState.shapes, readyState.shared, readyState.base⟩
  refine ⟨before, pointer, ready, callee, post, lengthBound, precheckRun, copied, entry, readyHeap,
    copied.2.2.1, pCell, lenCell, returned, (by rw [restored, innerEq]), heapCell, ?_⟩
  intro selected other
  have frame := precheck_global selected source.code initial.arena.code source rfl
  rw [precheckRun] at frame
  exact (copied_global input before ready pointer (input.length % 2^64) _ copied selected other).trans (congrArg Prod.snd frame)

end InitECandidate.Solver.Input.CurrentStartup.DecoderInput

#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.Stateless.original_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.Stateless.environment
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.Stateless.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.copied_global
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.copied_state
#print axioms InitECandidate.Solver.Input.CurrentStartup.DecoderInput.stateless_reached
