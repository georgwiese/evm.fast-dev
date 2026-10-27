import InitECandidate.Solver.Input.CurrentStartup.Prefix
import InitECandidate.Solver.Input.InitializerNormal

namespace InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def shaActions : List InitializerAllocations.Action := [InitializerAllocations.constant "sha_st" 64, InitializerAllocations.constant "sha_pad" 128]
def keccakActions : List InitializerAllocations.Action :=
  [InitializerAllocations.constant "keccak_rc" 192, InitializerAllocations.constant "keccak_st" 200, InitializerAllocations.constant "keccak_pad" 136]
def sszActions : List InitializerAllocations.Action :=
  [InitializerAllocations.constant "ssz_len_chunk" 32, InitializerAllocations.constant "ssz_offs" 64,
    ⟨"zero_hashes", 2048, .panop .mul [.const 64#64, .const 32#64]⟩]

def keccakTail : ProgHOL 64 := seqTail 3 (Code.body .keccak_init)
def sszAfterGuard : ProgHOL 64 := seqTail 1 (Code.body .ssz_init)
def sszTail : ProgHOL 64 := seqTail 3 sszAfterGuard

theorem sha_shape : Code.body .sha256_init = InitializerAllocations.withTail shaActions (.return (.const 0#64)) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_sha256_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none, InitializerAllocations.withTail, shaActions, InitializerAllocations.call, InitializerAllocations.constant]

theorem keccak_shape : Code.body .keccak_init = InitializerAllocations.withTail keccakActions keccakTail := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_keccak_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none, InitializerAllocations.withTail, keccakActions, InitializerAllocations.call, InitializerAllocations.constant,
    keccakTail, seqTail]

theorem ssz_shape : sszAfterGuard = InitializerAllocations.withTail sszActions sszTail := by
  simp only [sszAfterGuard, sszTail, seqTail, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_init,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none,
    InitializerAllocations.withTail, sszActions, InitializerAllocations.call, InitializerAllocations.constant]

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem keccak_rc_member : ofString "keccak_rc" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem sha_valid (action : InitializerAllocations.Action) (member : action ∈ shaActions) : InitializerAllocations.Valid action := by
  simp only [shaActions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.sha_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.sha_names.2 (by decide) (by decide)

theorem keccak_valid (action : InitializerAllocations.Action) (member : action ∈ keccakActions) : InitializerAllocations.Valid action := by
  simp only [keccakActions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InitializerAllocations.valid_constant _ _ keccak_rc_member (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.keccak_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.keccak_names.2 (by decide) (by decide)

theorem ssz_valid (action : InitializerAllocations.Action) (member : action ∈ sszActions) : InitializerAllocations.Valid action := by
  simp only [sszActions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.ssz_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant _ _ OriginalScalarGlobals.ssz_names.2.1 (by decide) (by decide)
  · refine ⟨OriginalScalarGlobals.ssz_names.2.2, by decide, by decide, ?_⟩
    intro source
    rfl

theorem actions_small (actions : List InitializerAllocations.Action)
    (member : actions = shaActions ∨ actions = keccakActions ∨ actions = sszActions) :
    ∀ action ∈ actions, action.bytes < 2^64 := by
  intro action inside
  rcases member with rfl | rfl | rfl
  · simp only [shaActions, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> decide
  · simp only [keccakActions, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> decide
  · simp only [sszActions, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> decide

/-- The post-allocation Keccak literal stores retain every global even when
an ordinary store fails. No mapped table or successful store is assumed. -/
theorem keccak_tail_global (selected : MlS) (code) : GlobalEffects.Preserves selected code keccakTail := by
  simp only [keccakTail, seqTail, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_keccak_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  repeat' first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.store selected code _ _
    | exact GlobalEffects.returned selected code _

/-- An actual SHA initializer return determines its real global bindings
and heap cursor directly from the two literal allocation calls. -/
theorem sha_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .sha256_init) = (some (.returned value), target)) :
    cursor + 192 ≤ 2952790016 ∧
      target = emptyLocalsHOLFinite {InitializerAllocations.template source cursor shaActions with clock := source.clock - 2} := by
  rw [sha_shape] at actual
  obtain ⟨middle, prefixRun, tailRun⟩ := InitializerAllocations.prefix_return source target shaActions (.return (.const 0#64)) value actual
  obtain ⟨room, stateEq⟩ := InitializerAllocations.normal_prefix source middle cursor shaActions installed scalars heap sha_valid
    (actions_small shaActions (Or.inl rfl)) bounded aligned prefixRun
  have returned := WitnessRadix.BuildEntry.zero_return middle
  simp only [WitnessRadix.BuildEntry.returnZero] at returned
  rw [returned] at tailRun
  have postEq : target = emptyLocalsHOLFinite middle := (congrArg Prod.snd tailRun).symm
  refine ⟨by simpa [shaActions, InitializerAllocations.totalBytes, InitializerAllocations.constant] using room, ?_⟩
  rw [postEq, stateEq]
  rfl

/-- A real Keccak initializer return retains its exact allocated globals.
Only ordinary memory can change in its actual literal table-writing suffix. -/
theorem keccak_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .keccak_init) = (some (.returned value), target)) :
    cursor + 528 ≤ 2952790016 ∧
      ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor keccakActions).globals.lookup selected := by
  rw [keccak_shape] at actual
  obtain ⟨middle, prefixRun, tailRun⟩ := InitializerAllocations.prefix_return source target keccakActions keccakTail value actual
  obtain ⟨room, stateEq⟩ := InitializerAllocations.normal_prefix source middle cursor keccakActions installed scalars heap keccak_valid
    (actions_small keccakActions (Or.inr (Or.inl rfl))) bounded aligned prefixRun
  refine ⟨by simpa [keccakActions, InitializerAllocations.totalBytes, InitializerAllocations.constant] using room, ?_⟩
  intro selected
  have preserved := keccak_tail_global selected middle.code middle rfl
  rw [tailRun] at preserved
  rw [stateEq] at preserved
  exact congrArg Prod.snd preserved

/-- The literal zero-hash guard falls through from its real declared zero.
This excludes the initializer's early-return branch at the actual first call. -/
theorem ssz_guard_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (Code.body .ssz_init) = evaluateHOLFiniteState source sszAfterGuard := by
  have shape : Code.body .ssz_init = .seq
      (.ite (.cmp .notEqual (.var .global (ofString "zero_hashes")) (.const 0#64))
        (.return (.const 0#64)) .skip) sszAfterGuard := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_ssz_init, progToHOL, expToHOL, shapeToHOL,
      List.map_cons, List.map_nil, Option.map_some, Option.map_none, sszAfterGuard, seqTail]
  rw [shape, evaluateHOLFiniteState_seq_line780]
  have guardRun : evaluateHOLFiniteState source
      (.ite (.cmp .notEqual (.var .global (ofString "zero_hashes")) (.const 0#64))
        (.return (.const 0#64)) .skip) = (none, source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [evalHOLExact, toExact, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, evaluateHOLFiniteState_skip]
  rw [guardRun]

theorem ssz_tail_global (selected : MlS) (code) : GlobalEffects.Preserves selected code sszTail := by
  simp only [sszTail, sszAfterGuard, seqTail, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_ssz_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  repeat' first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.store selected code _ _
    | exact GlobalEffects.returned selected code _

/-- The first actual SSZ initialization allocates the real64-byte offset
workspace. Its table stores retain these globals; no future table access is
assumed readable, nor is an aggregate allocation budget supplied. -/
theorem ssz_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (Code.body .ssz_init) = (some (.returned value), target)) :
    cursor + 2144 ≤ 2952790016 ∧
      ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor sszActions).globals.lookup selected := by
  rw [ssz_guard_zero source zero, ssz_shape] at actual
  obtain ⟨middle, prefixRun, tailRun⟩ := InitializerAllocations.prefix_return source target sszActions sszTail value actual
  obtain ⟨room, stateEq⟩ := InitializerAllocations.normal_prefix source middle cursor sszActions installed scalars heap ssz_valid
    (actions_small sszActions (Or.inr (Or.inr rfl))) bounded aligned prefixRun
  refine ⟨by simpa [sszActions, InitializerAllocations.totalBytes, InitializerAllocations.constant] using room, ?_⟩
  intro selected
  have preserved := ssz_tail_global selected middle.code middle rfl
  rw [tailRun] at preserved
  rw [stateEq] at preserved
  exact congrArg Prod.snd preserved

end InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.sha_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_shape
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_rc_member
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.sha_valid
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_valid
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_valid
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.actions_small
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_tail_global
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.sha_return
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_return

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_guard_zero
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_tail_global
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_return
