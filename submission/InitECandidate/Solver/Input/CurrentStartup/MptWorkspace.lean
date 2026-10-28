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
