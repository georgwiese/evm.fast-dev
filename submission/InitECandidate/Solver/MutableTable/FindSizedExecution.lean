import InitECandidate.Solver.MutableTable.FindPrepared
import InitECandidate.Solver.MutableTable.FindSizedBuild
import InitECandidate.Solver.MutableTable.HashSizedMapped

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Complete unchanged account/storage lookup, including header reads, actual
hash, masked start, every probe, return and declaration scopes. The occupied
slot count permits adversarial collisions; no hash distribution is assumed.
These are source evaluator clocks, with original entry premises explicit. -/
theorem sized_find (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (kind : HashSized.Kind) (cells : HeaderCells source table p)
    (keyLength : p.keyLength = BitVec.ofNat 64 (HashSized.keySize kind))
    (bits : Nat) (small : bits < 64) (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits))
    (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 0 ∨ usedByte source p (BitVec.ofNat 64 i)=some 1)
    (covered : ∀ i<2^bits,usedByte source p (BitVec.ofNat 64 i)=some 1→i∈order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + HashSized.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (enough : sizedProbePrice kind * order.length + 1 ≤ source.clock) :
    ∃ paid value, paid ≤ sizedProbePrice kind * order.length + 1 ∧ value.toNat ≤ p.capacity.toNat ∧
      (evaluateHOLFiniteState source body).1 = some (.returned (.val (.word value))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source body).2 = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  classical
  let headers := headerState source p
  have distinct : ([ofString "used", ofString "keys", ofString "stride", ofString "klen", ofString "cap", ofString "key"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil] at distinct
  have keyH : headers.locals.lookup (ofString "key") = some (.val (.word p.key)) := by
    have keyLocal := cells.keyLocal
    simp_all [headers, headerState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have klenH : headers.locals.lookup (ofString "klen") = some (.val (.word (BitVec.ofNat 64 (HashSized.keySize kind)))) := by
    simp_all [headers, headerState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have args : evalListHOLFinite headers (h := fun address => Classical.propDecidable (headers.memaddrs address))
      [localVar "key", localVar "klen"] = some (HashSized.values kind p.key) := by
    simp [HashSized.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, keyH, klenH]
  obtain ⟨hash, hashRun⟩ := HashSized.call_of_mapped headers kind p.key "h" [localVar "key", localVar "klen"] afterHash
    args hashCode queryFits queryMapped (by change 1 ≤ source.clock; omega)
  let index := hash &&& (p.capacity - 1#64)
  let start := hash.toNat % (2 ^ bits)
  let hashEntered := bind {headers with clock := source.clock - 1} "h" hash
  let entered := prepared source p hash index
  have startInside : start < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos bits)
  have indexEq : index = pathIndex bits start 0 := masked_start p hash bits small capacity
  have locals : Locals entered p (pathIndex bits start 0) := by
    rw [← indexEq]
    exact prepared_locals source p hash index cells.keyLocal
  obtain ⟨paid, value, post, bound, valueBound, tailRun, frame⟩ := sized_scan_count_bound entered p kind bits start small startInside
    capacity order room locals keyLength binary covered fits mapped queryFits queryMapped memeqCode
    (by change sizedProbePrice kind * order.length ≤ source.clock - 1; omega)
  have iRun : evaluateHOLFiniteState hashEntered afterHash =
      (some (.returned (.val (.word value))), restore hashEntered "i" post) := by
    rw [afterHash]
    exact Input.ScalarScope.declare_execute hashEntered post "i" initialIndex index afterIndex _ (initial_index_read source p hash) tailRun
  change evaluateHOLFiniteState headers hashCall =
    (let output := evaluateHOLFiniteState hashEntered afterHash; (output.1, restore headers "h" output.2)) at hashRun
  rw [iRun] at hashRun
  obtain ⟨restoreStack, setup⟩ := header_executes source table p cells
  have prefixRun := WitnessRadix.ProgramPrefix.execute setup hashCall
  have whole : evaluateHOLFiniteState source body = (some (.returned (.val (.word value))),
      restoreStack (restore headers "h" (restore hashEntered "i" post))) := by
    rw [header_shape, prefixRun, hashRun]
  refine ⟨paid + 1, value, by omega, valueBound, ?_, ?_⟩
  · rw [whole]
  · rw [whole, WitnessRadix.ProgramPrefix.restoration_frame setup]
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)}
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    have canonical : emptyLocalsHOLFinite {entered with clock := entered.clock - paid} =
        emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)} := by
      change emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} =
        emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)}
      rw [subtract]
    exact frame.trans canonical

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.sized_find
