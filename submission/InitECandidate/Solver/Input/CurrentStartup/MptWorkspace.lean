import InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspaceCalls
import InitECandidate.Solver.CurrentKeccak.Globals

namespace InitECandidate.Solver.Input.CurrentStartup.MptWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def actions : List InitializerAllocations.Action :=
  [InitializerAllocations.constant "empty_trie_root" 32,InitializerAllocations.constant "empty_code_hash" 32,
   InitializerAllocations.constant "mpt_nib_scratch" 64,InitializerAllocations.constant "mpt_hash_scratch" 40,
   InitializerAllocations.constant "mpt_key_scratch" 16]
def tail : ProgHOL 64 := seqTail 5 (Code.body .mpt_init)

set_option maxRecDepth 100000 in
theorem shape : Code.body .mpt_init = InitializerAllocations.withTail actions tail := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_mpt_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    actions,tail,seqTail,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant]

theorem valid (action : InitializerAllocations.Action) (member : action ∈ actions) : InitializerAllocations.Valid action := by
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.mpt_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.mpt_names.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.mpt_names.2.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.mpt_names.2.2.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.mpt_names.2.2.2.2 (by decide) (by decide)

theorem small (action : InitializerAllocations.Action) (member : action ∈ actions) : action.bytes < 2^64 := by
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem tail_globals (selected : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves selected code tail := by
  simp only [tail,seqTail,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_mpt_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  apply GlobalEffects.sequence
  · exact GlobalEffects.byte_store selected code _ _
  · apply GlobalEffects.sequence
    · exact GlobalEffects.call_body selected code (some none) (ofString "keccak256") _ CurrentKeccak.Hash.formals CurrentKeccak.Hash.body .one
        (CurrentKeccak.Hash.original_code code installed) (CurrentKeccak.hash_globals selected code installed)
    · apply GlobalEffects.sequence
      · exact GlobalEffects.call_body selected code (some none) (ofString "keccak256") _ CurrentKeccak.Hash.formals CurrentKeccak.Hash.body .one
          (CurrentKeccak.Hash.original_code code installed) (CurrentKeccak.hash_globals selected code installed)
      · exact GlobalEffects.returned selected code _

/-- A genuine normal current MPT initializer derives all five allocations,
its exact global layout and actual persistent room. Its real hash suffix
preserves those globals; no hash completion or future allocation is assumed. -/
theorem returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor%8 = 0) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Code.body .mpt_init) = (some (.returned value),post)) :
    cursor+184 ≤ 2952790016 ∧ ∀ selected,
      post.globals.lookup selected = (InitializerAllocations.template source cursor actions).globals.lookup selected := by
  rw [shape] at normal
  obtain ⟨middle,prefixRun,tailRun⟩ := InitializerAllocations.prefix_return source post actions tail value normal
  obtain ⟨room,stateEq⟩ := InitializerAllocations.normal_prefix source middle cursor actions installed scalars heap valid small bounded aligned prefixRun
  have codeEq := (evaluation_fields source middle _ none prefixRun).2.2.2
  refine ⟨by simpa [actions,InitializerAllocations.totalBytes,InitializerAllocations.constant] using room,?_⟩
  intro selected
  have kept := tail_globals selected source.code installed middle codeEq
  rw [tailRun] at kept
  have globals := congrArg Prod.snd kept
  change post.globals.lookup selected = middle.globals.lookup selected at globals
  rw [stateEq] at globals
  exact globals

theorem caller (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor%8 = 0)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .mpt_init) []) = (none,post)) :
    cursor+184 ≤ 2952790016 ∧ ∀ selected,
      post.globals.lookup selected = (InitializerAllocations.template source cursor actions).globals.lookup selected := by
  obtain ⟨entry,target,value,same,entryCode,bodyRun,callerGlobals⟩ := EarlyWorkspace.caller_return source post .mpt_init installed normal
  obtain ⟨room,layout⟩ := returned entry target cursor entryCode (by rw [same]; exact scalars) (by rw [same]; exact heap) bounded aligned value bodyRun
  refine ⟨room,?_⟩
  intro selected
  rw [callerGlobals,layout]
  exact congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup selected)
    (EarlyWorkspace.template_globals entry source cursor actions same)

end InitECandidate.Solver.Input.CurrentStartup.MptWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.returned
#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.caller

namespace InitECandidate.Solver.Input.CurrentStartup.U256Workspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def actions : List InitializerAllocations.Action:=[InitializerAllocations.constant "u256_ws" 640]

theorem shape : Code.body .u256_ws_init=.seq
    (.ite (.cmp .equal (.var .global (ofString "u256_ws")) (.const 0#64))
      (InitializerAllocations.call (InitializerAllocations.constant "u256_ws" 640)) .skip)
    (.return (.const 0#64)) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_u256_ws_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    InitializerAllocations.call,InitializerAllocations.constant]

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem workspace_member : ofString "u256_ws" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem valid (action : InitializerAllocations.Action) (member : action ∈ actions) : InitializerAllocations.Valid action := by
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst action
  exact InitializerAllocations.valid_constant _ _ workspace_member (by decide) (by decide)

private theorem selected (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (zero : source.globals.lookup (ofString "u256_ws")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (Code.body .u256_ws_init)=evaluateHOLFiniteState source (InitializerAllocations.program actions) := by
  rw [shape]
  simp [actions,InitializerAllocations.program,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,
    evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- A normal first initialization derives its actual640-byte allocation,
persistent room and exact post-state from the current allocator call. -/
theorem returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "u256_ws")=some (.val (.word 0#64)))
    (bounded : cursor≤2952790016) (aligned : cursor%8=0) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (Code.body .u256_ws_init)=(some (.returned value),target)) :
    cursor+640≤2952790016 ∧
      target=emptyLocalsHOLFinite {InitializerAllocations.template source cursor actions with clock:=source.clock-1} := by
  rw [selected source zero,InitializerAllocations.program_tail] at normal
  obtain ⟨middle,prefixRun,tailRun⟩:=InitializerAllocations.prefix_return source target actions (.return (.const 0#64)) value normal
  obtain ⟨room,stateEq⟩:=InitializerAllocations.normal_prefix source middle cursor actions installed scalars heap valid
    (by intro action member;simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member;subst action;decide)
    bounded aligned prefixRun
  have returned:=BuildEntry.zero_return middle
  simp only [BuildEntry.returnZero] at returned
  rw [returned] at tailRun
  have targetEq : target=emptyLocalsHOLFinite middle:=(congrArg Prod.snd tailRun).symm
  refine ⟨by simpa [actions,InitializerAllocations.totalBytes,InitializerAllocations.constant] using room,?_⟩
  rw [targetEq,stateEq]
  rfl

/-- The actual normally continuing ignored caller establishes the real
workspace pointer and heap layout, without a supplied future helper return. -/
theorem caller (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "u256_ws")=some (.val (.word 0#64)))
    (bounded : cursor≤2952790016) (aligned : cursor%8=0)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .u256_ws_init) [])=(none,target)) :
    cursor+640≤2952790016 ∧ ∀ selected,
      target.globals.lookup selected=(InitializerAllocations.template source cursor actions).globals.lookup selected := by
  obtain ⟨entry,post,value,same,entryCode,bodyRun,callerGlobals⟩:=EarlyWorkspace.caller_return source target .u256_ws_init installed normal
  obtain ⟨room,state⟩:=returned entry post cursor entryCode (by rw [same];exact scalars) (by rw [same];exact heap)
    (by rw [same];exact zero) bounded aligned value bodyRun
  refine ⟨room,?_⟩
  intro selected
  rw [callerGlobals,state]
  exact congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64)=>globals.lookup selected)
    (EarlyWorkspace.template_globals entry source cursor actions same)

theorem template_workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor actions).globals.lookup (ofString "u256_ws")=
      some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp [actions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,
    putGlobal,HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Input.CurrentStartup.U256Workspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.workspace_member
#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.valid
#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.returned
#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.caller
#print axioms InitECandidate.Solver.Input.CurrentStartup.U256Workspace.template_workspace
