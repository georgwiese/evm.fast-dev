import InitECandidate.Solver.Headers.ValidateLoopReturned
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A numerical upper frontier for the actual heap binding. -/
def HeapBound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bound : Nat) : Prop :=
  ∀ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) → heap.toNat≤bound

theorem HeapBound.mono (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : Nat)
    (bound : HeapBound source first) (ordered : first≤second) : HeapBound source second := by
  intro heap cell
  exact (bound heap cell).trans ordered

/-- Everything after the actual header decoder call preserves every global,
including the heap. Hashing writes its real buffers and FFI state only. -/
theorem after_header_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code afterHeader := by
  obtain ⟨_,_,_,_,_,_,_,_,headerShape,_,_⟩ := shapes
  rw [headerShape]
  apply Input.GlobalEffects.sequence
  · exact Input.GlobalEffects.store key code _ _
  · apply Input.GlobalEffects.sequence
    · exact Input.GlobalEffects.call_body key code (some none) (ofString "keccak256") hashArguments Keccak256.formals Keccak256.body .one
        (Keccak256.original_code code installed)
        (Keccak256.globals key code (Zero.original_code code installed) (CopyGeneral.original_code code installed)
          (Keccak256.block_original_code code installed) (Keccak256.permutation_original_code code installed))
    · exact Input.GlobalEffects.assign key code _ _

/-- Each actual normal row consumes at most368 bytes of persistent RLP
slice records and248 bytes for its header. The21/23 guard supplies the cap. -/
theorem decode_step_heap (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index bound : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count)
    (bounded : HeapBound source bound) (normal : evaluateHOLFiniteState source decodeStep=(none,post)) : HeapBound post (bound+616) := by
  obtain ⟨heap,heapCell,heapBound,heapAligned,before,lower⟩ := state.header_context data origin source index layout inside
  have args:=state.rows.read source data.array data.pointers data.lengths data.count data.lower data.upper index inside state.arena.domain state.arrayCell state.indexCell
  obtain ⟨_,_,_,_,_,_,_,decodeShape,_,_,_⟩ := shapes
  rw [decodeShape] at normal
  obtain ⟨target,header,inner,returned,continued,endpoint⟩ := Decode.scoped_normal source post (data.pointers index) (data.lengths index) heap data.cursor data.limit data.lower "h" decodeArguments afterHeader args state.arena heapCell heapBound before
    (state.rows.sizeBound index inside) lower heapAligned layout.lowerAligned layout.scratchBefore (state.rows.inputAfter index inside) state.installed state.shape normal
  let ready:=Input.CallNormal.continuationEntry source target "h" (.val (.word header))
  have pure:=after_header_globals (ofString "heap_ptr") ready.code (by change Input.OriginalCode.Installed target.code; rw [returned.code]; exact state.installed) ready rfl
  rw [continued] at pure
  have finalCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded header 248#64))) := by
    rw [endpoint]
    exact (congrArg Prod.snd pure).trans returned.heapGlobal
  intro current cell
  have same : current=PersistentAlloc.rounded header 248#64 := by
    have h:=Option.some.inj (cell.symm.trans finalCell)
    cases h
    rfl
  rw [same]
  exact returned.growth.trans (Nat.add_le_add_right (bounded heap heapCell) 616)

/-- Actual first-loop normal execution aggregates the per-header frontier,
using its genuine small counter; no bound on future allocations is assumed. -/
theorem decode_loop_heap (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : Nat)
    (state : RoundState data origin source 0) (layout : RoundLayout data) (bounded : HeapBound source base)
    (normal : evaluateHOLFiniteState source (.while test decodeStep)=(none,post)) : HeapBound post (base+616*data.count) := by
  let invariant:=fun current=>∃ index,index≤data.count ∧ RoundState data origin current index ∧ HeapBound current (base+616*index)
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) decodeStep=(none,target) → invariant target := by
    intro current codeEq valid word read nonzero funded target bodyRun
    obtain ⟨index,indexBound,currentState,currentHeap⟩ := valid
    have active:=active_of_test data origin current index currentState layout (by omega) word read nonzero
    have entryState:=currentState.dec_clock data origin current index
    have next:=decode_step_normal data origin (decClockHOLFinite current) target index entryState layout active bodyRun
    have nextHeap:=decode_step_heap data origin (decClockHOLFinite current) target index (base+616*index) entryState layout active currentHeap bodyRun
    refine ⟨index+1,by omega,next,?_⟩
    have sum : base+616*index+616=base+616*(index+1) := by omega
    rwa [←sum]
  have initial : invariant source := ⟨0,by omega,state,by simpa using bounded⟩
  obtain ⟨index,indexBound,finalState,finalHeap⟩ := Input.loop_invariant source.code (ofString "n") test decodeStep decode_step_local invariant step source post rfl initial normal
  exact finalHeap.mono post _ _ (by omega)

theorem after_decode_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code afterDecode := by
  obtain ⟨_,_,_,_,_,resetShape,tailShape,_,_,_,_⟩ := shapes
  rw [resetShape,tailShape]
  exact Input.GlobalEffects.sequence key code _ _ (Input.GlobalEffects.assign key code _ _)
    (Input.GlobalEffects.sequence key code _ _
      (Input.GlobalEffects.loop key code _ _ (Input.GlobalEffects.of_readonly key code _ (link_step_readonly code installed)))
      (Input.GlobalEffects.returned key code _))

/-- The reset, comparison loop and tuple return do not grow the heap. -/
theorem loops_heap (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (base : Nat)
    (state : RoundState data origin source 0) (layout : RoundLayout data) (bounded : HeapBound source base)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loops=(some (.returned value),post)) : HeapBound post (base+616*data.count) := by
  obtain ⟨_,_,_,_,loopsShape,_,_,_,_,_,_⟩ := shapes
  rw [loopsShape] at normal
  obtain ⟨middle,loopRun,continued⟩ := Input.sequence_returned source post _ _ value (decode_loop_never source) normal
  have middleBound:=decode_loop_heap data origin source middle base state layout bounded loopRun
  have fields:=Input.evaluation_fields source middle _ none loopRun
  have pure:=after_decode_globals (ofString "heap_ptr") middle.code (by rw [fields.2.2.2]; exact state.installed) middle rfl
  rw [continued] at pure
  intro heap cell
  exact middleBound heap ((congrArg Prod.snd pure).symm.trans cell)

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.after_header_globals
#print axioms InitECandidate.Solver.Headers.Validate.decode_step_heap
#print axioms InitECandidate.Solver.Headers.Validate.decode_loop_heap
#print axioms InitECandidate.Solver.Headers.Validate.after_decode_globals
#print axioms InitECandidate.Solver.Headers.Validate.loops_heap
