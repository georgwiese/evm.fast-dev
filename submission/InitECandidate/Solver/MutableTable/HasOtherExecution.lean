import InitECandidate.Solver.MutableTable.HasProgram
import InitECandidate.Solver.MutableTable.FindOtherCall

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Entire original indexed-key membership body, with actual probes and
return. Table representation and caller reachability remain explicit. -/
theorem other_has (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (width : Nat) (smallWidth : width ≤ 64) (not20 : width ≠ 20) (not32 : width ≠ 32) (not52 : width ≠ 52) (cells : Find.HeaderCells source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (width))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ Find.usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,Find.usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + width < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + width < 2 ^ 64)
    (queryMapped : ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (enough : Find.otherProbePrice width * order.length + (MemeqByteRuntime.price width + 2) ≤ source.clock) :
    ∃ paid answer target, paid ≤ Find.otherProbePrice width * order.length + (MemeqByteRuntime.price width + 2) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word answer))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", localVar "key"] = some [.val (.word table), .val (.word p.key)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, cells.tableLocal, cells.keyLocal]
  obtain ⟨paid, index, bound, indexBound, callRun⟩ := Find.other_call source table p width smallWidth not20 not32 not52
    ⟨cells.mapped, cells.capacity, cells.keyLength, cells.stride, cells.keys, cells.used⟩ keyLength bits small capacity order room
    binary covered fits mapped queryFits queryMapped hashCode memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args enough
  let entered := bind {source with clock := source.clock - paid} "i" index
  have tEntered : entered.locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other _ "i" "t" _ (by decide)).trans cells.tableLocal
  have tailRun := tail_execute entered table index p.capacity tEntered (bind_lookup_same _ _ _) (cells.mapped 16 (by simp)) cells.capacity
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex) =
    (let result := evaluateHOLFiniteState entered afterIndex; (result.1, restore source "i" result.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨paid, (if index = p.capacity then 0#64 else 1#64), restore source "i" (emptyLocalsHOLFinite entered), bound, ?_, ?_, rfl⟩
  · split <;> simp
  · rw [body_shape]
    exact callRun

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.other_has
