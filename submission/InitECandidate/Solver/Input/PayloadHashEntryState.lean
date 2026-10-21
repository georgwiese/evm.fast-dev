import InitECandidate.Solver.Input.PayloadHashStaticPrefix

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.PayloadHash.Entry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Ready (data : Description) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (out cursor stp accel chunk zeros : BitVec 64) : Prop where
  workspace : SszHash.Workspace current stp accel chunk zeros
  payload : current.locals.lookup (ofString "pl")=some (.val (.word data.payload))
  output : current.locals.lookup (ofString "out")=some (.val (.word out))
  heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  input : HashInput.Frame origin current lower upper

def rawEntry (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "raw" data.raw
def markEntry (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  bind {rawEntry data source with clock:=source.clock-1} "mark" cursor
def chunksEntry (data : Description) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  bind (PersistentAlloc.post {markEntry data source cursor with clock:=source.clock-1-1} cursor 608#64) "ch" cursor
def restoreEntry (data : Description) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  restore source "raw" (restore (rawEntry data source) "mark" (restore (markEntry data source cursor) "ch" post))

theorem rounded_cursor (data : Description) (budget : Nat) (cursor : BitVec 64) (geometry : data.RuntimeGeometry budget cursor) :
    PersistentAlloc.rounded cursor 608#64=chunksCursor cursor := by
  have room := geometry.arena.upper
  have aligned := geometry.aligned
  have number : (chunksCursor cursor).toNat=cursor.toNat+608 := byteAddress_toNat cursor 608 (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat cursor 608#64 (by change cursor.toNat+608+7<2^64; omega),number]
  change (cursor.toNat+608+7)/8*8=cursor.toNat+608
  omega

/-- Actual outer raw/mark/ch bindings and original allocator post-state
establish the complete payload hash caller/input relation. -/
theorem chunks_state (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (out cursor stp accel chunk zeros : BitVec 64)
    (actual : Ready data origin source lower upper out cursor stp accel chunk zeros)
    (geometry : data.RuntimeGeometry budget cursor) :
    StaticFields.State origin (chunksEntry data source cursor) lower upper data.payload data.raw cursor out (chunksCursor cursor) cursor stp accel chunk zeros := by
  have workspace := SszHash.Workspace.of_fields source (chunksEntry data source cursor) stp accel chunk zeros actual.workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 608#64)))).lookup key=source.globals.lookup key
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have pointer : (chunksEntry data source cursor).locals.lookup (ofString "raw")=some (.val (.word data.raw)) :=
    (bind_lookup_other _ "ch" "raw" cursor (by decide)).trans ((bind_lookup_other _ "mark" "raw" cursor (by decide)).trans (bind_lookup_same source "raw" data.raw))
  have output : (chunksEntry data source cursor).locals.lookup (ofString "out")=some (.val (.word out)) :=
    (bind_lookup_other _ "ch" "out" cursor (by decide)).trans ((bind_lookup_other _ "mark" "out" cursor (by decide)).trans ((bind_lookup_other source "raw" "out" data.raw (by decide)).trans actual.output))
  have payload : (chunksEntry data source cursor).locals.lookup (ofString "pl")=some (.val (.word data.payload)) :=
    (bind_lookup_other _ "ch" "pl" cursor (by decide)).trans ((bind_lookup_other _ "mark" "pl" cursor (by decide)).trans ((bind_lookup_other source "raw" "pl" data.raw (by decide)).trans actual.payload))
  have saved : (chunksEntry data source cursor).locals.lookup (ofString "mark")=some (.val (.word cursor)) :=
    (bind_lookup_other _ "ch" "mark" cursor (by decide)).trans (bind_lookup_same _ "mark" cursor)
  have heap : (chunksEntry data source cursor).globals.lookup (ofString "heap_ptr")=some (.val (.word (chunksCursor cursor))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 608#64)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,rounded_cursor data budget cursor geometry]
  exact ⟨⟨workspace,pointer,bind_lookup_same _ "ch" cursor,output,saved,heap⟩,payload,⟨actual.input.words⟩⟩

end InitECandidate.Solver.Input.PayloadHash.Entry
#print axioms InitECandidate.Solver.Input.PayloadHash.Entry.rounded_cursor
#print axioms InitECandidate.Solver.Input.PayloadHash.Entry.chunks_state
