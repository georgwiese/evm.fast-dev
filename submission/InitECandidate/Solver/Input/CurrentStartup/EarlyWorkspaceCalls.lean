import InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Global templates depend only on the actual incoming global map, not
callee locals, caller locals or the separately paid clock. -/
theorem template_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (actions : List InitializerAllocations.Action) (same : source.globals = target.globals) :
    (InitializerAllocations.template source cursor actions).globals = (InitializerAllocations.template target cursor actions).globals := by
  induction actions generalizing source target cursor with
  | nil => exact same
  | cons action rest ih =>
    apply ih (InitializerAllocations.reserve source action cursor) (InitializerAllocations.reserve target action cursor) (cursor + action.bytes)
    change (source.globals.update _).update _ = (target.globals.update _).update _
    rw [same]

/-- A real continuing ignored startup call exposes its genuine returned
body and caller restoration. No helper completion is supplied separately. -/
theorem caller_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (routine : Code.Routine)
    (installed : OriginalCode.Installed source.code)
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name routine) []) = (none, target)) :
    ∃ entry post : PanSemStateFiniteExact 64 Guest.HostMemory, ∃ value, entry.globals = source.globals ∧ OriginalCode.Installed entry.code ∧
      evaluateHOLFiniteState entry (Code.body routine) = (some (.returned value), post) ∧ target.globals = post.globals := by
  obtain ⟨positive, values, body, callee, shape, post, value, args, called, returned, checked,
    restored, domain, little, shapes, code⟩ := CallNormal.ignored_data source target (Code.name routine) [] actual
  have bodyEq := GlobalEffects.lookup_body source.code (Code.name routine) (Code.formals routine) (Code.body routine)
    (Code.shape routine) (Code.installed source.code installed routine) values body callee shape called
  subst body
  exact ⟨callEntryStateHOLFinite source callee, post, value, rfl, installed, returned, by rw [restored]⟩

theorem sha_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0)
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .sha256_init) []) = (none, target)) :
    cursor + 192 ≤ 2952790016 ∧
      ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor shaActions).globals.lookup selected := by
  obtain ⟨entry, post, value, same, entryCode, bodyRun, callerGlobals⟩ := caller_return source target .sha256_init installed actual
  obtain ⟨room, bodyState⟩ := sha_return entry post cursor entryCode
    (by rw [same]; exact scalars) (by rw [same]; exact heap) bounded aligned value bodyRun
  refine ⟨room, ?_⟩
  intro selected
  rw [callerGlobals, bodyState]
  exact congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup selected)
    (template_globals entry source cursor shaActions same)

theorem keccak_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0)
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .keccak_init) []) = (none, target)) :
    cursor + 528 ≤ 2952790016 ∧
      ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor keccakActions).globals.lookup selected := by
  obtain ⟨entry, post, value, same, entryCode, bodyRun, callerGlobals⟩ := caller_return source target .keccak_init installed actual
  obtain ⟨room, written⟩ := keccak_return entry post cursor entryCode
    (by rw [same]; exact scalars) (by rw [same]; exact heap) bounded aligned value bodyRun
  refine ⟨room, ?_⟩
  intro selected
  rw [callerGlobals]
  exact (written selected).trans (congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup selected)
    (template_globals entry source cursor keccakActions same))

theorem ssz_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (bounded : cursor ≤ 2952790016) (aligned : cursor % 8 = 0)
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .ssz_init) []) = (none, target)) :
    cursor + 2144 ≤ 2952790016 ∧
      ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor sszActions).globals.lookup selected := by
  obtain ⟨entry, post, value, same, entryCode, bodyRun, callerGlobals⟩ := caller_return source target .ssz_init installed actual
  obtain ⟨room, written⟩ := ssz_return entry post cursor entryCode
    (by rw [same]; exact scalars) (by rw [same]; exact heap) (by rw [same]; exact zero) bounded aligned value bodyRun
  refine ⟨room, ?_⟩
  intro selected
  rw [callerGlobals]
  exact (written selected).trans (congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup selected)
    (template_globals entry source cursor sszActions same))

/-- Transfer all original scalar globals through a checked literal global
allocation template. This does not require successful later memory stores. -/
theorem written_scalars (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (actions : List InitializerAllocations.Action) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (written : ∀ selected, target.globals.lookup selected = (InitializerAllocations.template source cursor actions).globals.lookup selected) :
    OriginalScalarGlobals.Scalars target.globals := by
  intro selected member
  obtain ⟨word, present⟩ := InitializerAllocations.template_scalars source cursor actions scalars selected member
  exact ⟨word, (written selected).trans present⟩

end InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.template_globals
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.caller_return
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.sha_call
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.keccak_call
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.ssz_call
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.written_scalars
