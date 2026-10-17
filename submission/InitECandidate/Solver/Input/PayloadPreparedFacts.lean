import InitECandidate.Solver.Input.PayloadPrefixExtra

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem prepared_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor length : BitVec 64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    (prepared source input pointer cursor length).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) ∧
    (prepared source input pointer cursor length).locals.lookup (ofString "pl")=some (.val (.word cursor)) ∧
    (prepared source input pointer cursor length).locals.lookup (ofString "len")=some (.val (.word length)) := by
  have headerP : (headerStored source pointer cursor length).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "p" cursor (by decide)).trans p
  have headerPl : (headerStored source pointer cursor length).locals.lookup (ofString "pl")=some (.val (.word cursor)) := bind_lookup_same _ _ _
  have headerN : (headerStored source pointer cursor length).locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "len" cursor (by decide)).trans n
  exact ⟨(declared_other (headerStored source pointer cursor length) input "p" (by decide) (by decide) (by decide) (by decide)).trans headerP,
    (declared_other (headerStored source pointer cursor length) input "pl" (by decide) (by decide) (by decide) (by decide)).trans headerPl,
    (declared_other (headerStored source pointer cursor length) input "len" (by decide) (by decide) (by decide) (by decide)).trans headerN⟩

theorem prepared_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor length : BitVec 64) :
    (prepared source input pointer cursor length).globals.lookup (ofString "heap_ptr")=
      some (.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 136#64))) := by
  change (source.globals.update (ofString "heap_ptr",.val (.word (WitnessRadix.PersistentAlloc.rounded cursor 136#64)))).lookup (ofString "heap_ptr")=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem payload_array_geometry (input : Guest.InputBlob) (pointer cursor : BitVec 64)
    (aligned : cursor.toNat%8=0)
    (after : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (room : cursor.toNat+136+4*(input.length%2^64)≤33806089496) :
    (WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat=cursor.toNat+136 ∧
    (WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat%8=0 ∧
    pointer.toNat+input.length%2^64+8≤(WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat ∧
    (WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat+4*(input.length%2^64)≤33806089496 := by
  have number:=WitnessRadix.PersistentAlloc.rounded_nat cursor 136#64 (by change cursor.toNat+136+7<2^64; omega)
  change (WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat=(cursor.toNat+136+7)/8*8 at number
  have exactNumber : (WitnessRadix.PersistentAlloc.rounded cursor 136#64).toNat=cursor.toNat+136 := by omega
  exact ⟨exactNumber,by omega,by omega,by omega⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prepared_locals
#print axioms InitECandidate.Solver.Input.Payload.prepared_heap
#print axioms InitECandidate.Solver.Input.Payload.payload_array_geometry
