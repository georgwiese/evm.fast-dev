import InitECandidate.Solver.Input.RequestsHashReady

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real original list call preserves any actual request-metadata word.
Its full physical output/temporary separation is derived from current arenas. -/
theorem step_metadata (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity offset : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (separation : Separation rq stp accel chunk) (inside : offset<80)
    (run : evaluateHOLFiniteState source (step kind)=(none,post)) :
    post.memory (rq+BitVec.ofNat 64 offset)=source.memory (rq+BitVec.ofNat 64 offset) := by
  let query := rq+BitVec.ofNat 64 offset
  have number : query.toNat=rq.toNat+offset := byteAddress_toNat rq offset (by have h:=geometry.requestsArena.upper; omega)
  have before : query.toNat<ch.toNat := by rw [number]; have h:=geometry.requestsBefore; omega
  have below : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  obtain ⟨outArena,temporary⟩ := step_geometry rq ch cursor pointers counts capacity geometry kind
  have rootsAway := CopyGeneral.Away.after ch query 160 geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) before
  have protection := separation.at_metadata source rq stp accel chunk zeros offset inside ready.workspace geometry.requestsArena
  exact RequestListHash.call_memory source post kind (pointers kind) cursor (ch+BitVec.ofNat 64 (32*kind.tag)) stp accel chunk zeros query (counts kind)
    (by have a:=geometry.countsBound kind; have b:=geometry.bounded; omega) protection ready.heap (geometry.inputs kind) temporary geometry.aligned outArena below
    (CopyGeneral.Away.subrange ch query 160 (32*kind.tag) 32 rootsAway (by have h:=tag_bound kind; omega)) (arguments kind)
    (arguments_read source kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry) run

/-- The same observed normal list call retains all ten current pointer/count
cells, caller locals, initialized workspace and restored temporary heap. -/
theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (rq ch out cursor stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (separation : Separation rq stp accel chunk)
    (run : evaluateHOLFiniteState source (step kind)=(none,post)) : Ready post rq ch out cursor stp accel chunk zeros pointers counts := by
  obtain ⟨outArena,temporary⟩ := step_geometry rq ch cursor pointers counts capacity geometry kind
  have args := arguments_read source kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry
  have heap := RequestListHash.ignored_return_heap source post kind (pointers kind) cursor (ch+BitVec.ofNat 64 (32*kind.tag)) stp accel chunk zeros (counts kind)
    (by have a:=geometry.countsBound kind; have b:=geometry.bounded; omega) ready.workspace ready.heap (geometry.inputs kind) temporary geometry.aligned outArena (arguments kind) args run
  have workspace := SszHash.Workspace.after source post stp accel chunk zeros ready.workspace (step kind) none run
    (fun key different=>step_globals kind key source.code ready.workspace.sha.installed different)
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source post (ofString name) (ofString "htr_request_list") (arguments kind) run
  have image : Image post rq pointers counts := by
    constructor
    intro selected
    have tagBound := tag_bound selected
    have pFrame := step_metadata source post kind rq ch out cursor stp accel chunk zeros pointers counts capacity (16*selected.tag) ready geometry separation (by omega) run
    have nFrame := step_metadata source post kind rq ch out cursor stp accel chunk zeros pointers counts capacity (16*selected.tag+8) ready geometry separation (by omega) run
    exact ⟨pFrame.trans (ready.image.fields selected).1,nFrame.trans (ready.image.fields selected).2⟩
  exact ⟨workspace,(other "rq").trans ready.requests,(other "ch").trans ready.chunks,(other "out").trans ready.output,image,heap⟩

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.step_metadata
#print axioms InitECandidate.Solver.Input.RequestsHash.step_normal
