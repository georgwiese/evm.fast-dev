import InitECandidate.Solver.Input.RequestRootHashPipeline

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.RequestRootHash.Entry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Ready (data : Description) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (out ch stp accel chunk zeros : BitVec 64) : Prop where
  workspace : SszHash.Workspace current stp accel chunk zeros
  si : current.locals.lookup (ofString "si")=some (.val (.word data.si))
  output : current.locals.lookup (ofString "out")=some (.val (.word out))
  heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word ch))
  input : HashInput.Frame origin current lower upper

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) := bind {source with clock:=source.clock-1} "mark" ch
def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) :=
  bind (PersistentAlloc.post {marked source ch with clock:=source.clock-1-1} ch 128#64) "ch" ch
def restored (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) := restore source "mark" (restore (marked source ch) "ch" post)

theorem rounded_cursor (data : Description) (budget : Nat) (ch : BitVec 64) (geometry : data.RuntimeGeometry budget ch) : PersistentAlloc.rounded ch 128#64=cursor ch := by
  have room := geometry.arena.upper
  have aligned := geometry.aligned
  have number : (cursor ch).toNat=ch.toNat+128 := byteAddress_toNat ch 128 (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat ch 128#64 (by change ch.toNat+128+7<2^64; omega),number]
  change (ch.toNat+128+7)/8*8=ch.toNat+128
  omega

/-- Original outer heap mark and 128-byte roots allocation establish the
real shared-phase caller relation and retain the entire decoded region. -/
theorem allocated_ready (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out ch stp accel chunk zeros : BitVec 64) (actual : Ready data origin source lower upper out ch stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget ch) :
    RequestRootHash.Ready data origin (allocated source ch) lower upper ch out ch stp accel chunk zeros := by
  have workspace := SszHash.Workspace.of_fields source (allocated source ch) stp accel chunk zeros actual.workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 128#64)))).lookup key=source.globals.lookup key
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have si : (allocated source ch).locals.lookup (ofString "si")=some (.val (.word data.si)) :=
    (bind_lookup_other _ "ch" "si" ch (by decide)).trans ((bind_lookup_other _ "mark" "si" ch (by decide)).trans actual.si)
  have output : (allocated source ch).locals.lookup (ofString "out")=some (.val (.word out)) :=
    (bind_lookup_other _ "ch" "out" ch (by decide)).trans ((bind_lookup_other _ "mark" "out" ch (by decide)).trans actual.output)
  have saved : (allocated source ch).locals.lookup (ofString "mark")=some (.val (.word ch)) :=
    (bind_lookup_other _ "ch" "mark" ch (by decide)).trans (bind_lookup_same _ "mark" ch)
  have heap : (allocated source ch).globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor ch))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 128#64)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,rounded_cursor data budget ch geometry]
  exact ⟨workspace,si,bind_lookup_same _ "ch" ch,output,saved,heap,⟨actual.input.words⟩⟩

end InitECandidate.Solver.Input.RequestRootHash.Entry
#print axioms InitECandidate.Solver.Input.RequestRootHash.Entry.rounded_cursor
#print axioms InitECandidate.Solver.Input.RequestRootHash.Entry.allocated_ready
