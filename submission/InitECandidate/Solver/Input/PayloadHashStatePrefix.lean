import InitECandidate.Solver.Input.PayloadHashStateCall
import InitECandidate.Solver.Input.AllocationLocalNormal

namespace InitECandidate.Solver.Input.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Prefix-bound locals distinct from the retained original payload caller
bindings. These are lexical facts, not assumptions about later execution. -/
structure CallerOther (name : String) : Prop where
  payload : ofString name≠ofString "pl"
  raw : ofString name≠ofString "raw"
  chunks : ofString name≠ofString "ch"
  output : ofString name≠ofString "out"
  mark : ofString name≠ofString "mark"

theorem State.with_clock (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros) (clock : Nat) :
    State origin {source with clock:=clock} lower upper pl raw ch out cursor mark stp accel chunk zeros :=
  ⟨⟨SszHash.Workspace.of_fields source _ stp accel chunk zeros actual.ready.workspace rfl rfl (by intro key different; rfl),
    actual.ready.pointer,actual.ready.chunks,actual.ready.output,actual.ready.saved,actual.ready.heap⟩,actual.payload,⟨actual.input.words⟩⟩

/-- Real scalar declarations/assignments preserve every retained input and
caller fact when their binding is outside those original caller variables. -/
theorem State.bind_current (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros)
    (name : String) (value : BitVec 64) (other : CallerOther name) :
    State origin (bind source name value) lower upper pl raw ch out cursor mark stp accel chunk zeros :=
  ⟨⟨SszHash.Workspace.of_fields source _ stp accel chunk zeros actual.ready.workspace rfl rfl (by intro key different; rfl),
    (bind_lookup_other source name "raw" value other.raw).trans actual.ready.pointer,
    (bind_lookup_other source name "ch" value other.chunks).trans actual.ready.chunks,
    (bind_lookup_other source name "out" value other.output).trans actual.ready.output,
    (bind_lookup_other source name "mark" value other.mark).trans actual.ready.saved,actual.ready.heap⟩,
    (bind_lookup_other source name "pl" value other.payload).trans actual.payload,⟨actual.input.words⟩⟩

/-- The original allocator post-state changes only its actual heap global;
its decoded/input region and retained caller facts remain current. Clock
funding and the link to this post-state come from the actual allocation. -/
theorem State.allocator_post (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (pl raw ch out cursor mark stp accel chunk zeros : BitVec 64)
    (actual : State origin source lower upper pl raw ch out cursor mark stp accel chunk zeros) (amount : BitVec 64) :
    State origin (PersistentAlloc.post {source with clock:=source.clock-1} cursor amount) lower upper pl raw ch out (PersistentAlloc.rounded cursor amount) mark stp accel chunk zeros := by
  let target := PersistentAlloc.post {source with clock:=source.clock-1} cursor amount
  have workspace := SszHash.Workspace.of_fields source target stp accel chunk zeros actual.ready.workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor amount)))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have heap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor amount))) := by
    simp [target,PersistentAlloc.post,HolFiniteMapExact.lookup_update,FUPDATE]
  exact ⟨⟨workspace,actual.ready.pointer,actual.ready.chunks,actual.ready.output,actual.ready.saved,heap⟩,actual.payload,⟨actual.input.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.State.with_clock
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.State.bind_current
#print axioms InitECandidate.Solver.Input.PayloadHash.StaticFields.State.allocator_post
