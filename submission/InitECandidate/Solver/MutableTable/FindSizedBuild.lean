import InitECandidate.Solver.MutableTable.FindSizedLoop
import InitECandidate.Solver.MutableTable.MaskedPath

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Construct the physical runtime chain from actual occupied reads and
readable key regions along the original masked-index sequence. -/
theorem sized_chain_of_prefix (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (kind : HashSized.Kind)
    (indices : Nat → BitVec 64) (start length : Nat)
    (advance : ∀ j < start + length, indices (j + 1) = next p (indices j))
    (indicesInside : ∀ j ≤ start + length, (indices j).toNat < p.capacity.toNat)
    (occupied : ∀ j, start ≤ j → j < start + length → usedByte snapshot p (indices j) = some 1)
    (empty : usedByte snapshot p (indices (start + length)) = some 0)
    (fits : ∀ j, start ≤ j → j < start + length → (p.keys + indices j * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
    (mapped : ∀ j, start ≤ j → j < start + length → ∀ offset < HashSized.keySize kind,
      snapshot.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (p.keys + indices j * p.stride) offset))) :
    SizedChain snapshot p kind (indices start) length := by
  induction length generalizing start with
  | zero => exact .empty _ (indicesInside _ (by omega)) (by simpa using empty)
  | succ length ih =>
    have sum : start + 1 + length = start + (length + 1) := by omega
    have tail := ih (start + 1)
      (by intro j inside; exact advance j (by omega))
      (by intro j inside; exact indicesInside j (by omega))
      (by intro j lower upper; exact occupied j (by omega) (by omega))
      (by rw [sum]; exact empty)
      (by intro j lower upper; exact fits j (by omega) (by omega))
      (by intro j lower upper; exact mapped j (by omega) (by omega))
    rw [advance start (by omega)] at tail
    exact .occupied (indices start) 1 length (indicesInside _ (by omega)) (by decide)
      (occupied start (Nat.le_refl _) (by omega)) (fits start (Nat.le_refl _) (by omega))
      (mapped start (Nat.le_refl _) (by omega)) tail

/-- Binary used bytes and a covering order list supply a chain of at most
order.length occupied slots, even if every key hashes to the same start. -/
theorem sized_chain_of_order (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (kind : HashSized.Kind)
    (bits start : Nat) (small : bits < 64) (startInside : start < 2 ^ bits)
    (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits)) (order : List Nat) (room : order.length < 2 ^ bits)
    (binary : ∀ i < 2 ^ bits, usedByte snapshot p (BitVec.ofNat 64 i) = some 0 ∨ usedByte snapshot p (BitVec.ofNat 64 i) = some 1)
    (covered : ∀ i < 2 ^ bits, usedByte snapshot p (BitVec.ofNat 64 i) = some 1 → i ∈ order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < HashSized.keySize kind, snapshot.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset))) :
    ∃ length ≤ order.length, SizedChain snapshot p kind (pathIndex bits start 0) length := by
  obtain ⟨length, bounded, empty, occupied⟩ := first_empty snapshot p (2 ^ bits) start (Nat.two_pow_pos bits) startInside order room binary covered
  have capacityNumber : p.capacity.toNat = 2 ^ bits := by
    rw [capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) small)]
  refine ⟨length, bounded, ?_⟩
  exact sized_chain_of_prefix snapshot p kind (pathIndex bits start) 0 length
    (by intro j inside; exact path_advance p bits start j small capacity)
    (by intro j inside; rw [path_number bits start j small, capacityNumber]; exact Nat.mod_lt _ (Nat.two_pow_pos bits))
    (by intro j lower upper; exact occupied j (by omega))
    (by simpa only [Nat.zero_add, pathIndex] using empty)
    (by intro j lower upper; exact fits _ (Nat.mod_lt _ (Nat.two_pow_pos bits)))
    (by intro j lower upper; exact mapped _ (Nat.mod_lt _ (Nat.two_pow_pos bits)))

/-- Actual original mutable-key scan bound from occupied-count/order facts,
not a comparator oracle. Mutations must maintain those physical invariants. -/
theorem sized_scan_count_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (kind : HashSized.Kind)
    (bits start : Nat) (small : bits < 64) (startInside : start < 2 ^ bits)
    (capacity : p.capacity = BitVec.ofNat 64 (2 ^ bits)) (order : List Nat) (room : order.length < 2 ^ bits)
    (locals : Locals source p (pathIndex bits start 0)) (keyLength : p.keyLength = BitVec.ofNat 64 (HashSized.keySize kind))
    (binary : ∀ i < 2 ^ bits, usedByte source p (BitVec.ofNat 64 i) = some 0 ∨ usedByte source p (BitVec.ofNat 64 i) = some 1)
    (covered : ∀ i < 2 ^ bits, usedByte source p (BitVec.ofNat 64 i) = some 1 → i ∈ order)
    (fits : ∀ i < 2 ^ bits, (p.keys + BitVec.ofNat 64 i * p.stride).toNat + HashSized.keySize kind < 2 ^ 64)
    (mapped : ∀ i < 2 ^ bits, ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + BitVec.ofNat 64 i * p.stride) offset)))
    (queryFits : p.key.toNat + HashSized.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < HashSized.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (code : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (enough : sizedProbePrice kind * order.length ≤ source.clock) :
    ∃ (paid : Nat) (answer : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ sizedProbePrice kind * order.length ∧ answer.toNat ≤ p.capacity.toNat ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word answer))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  obtain ⟨length, bounded, chain⟩ := sized_chain_of_order source p kind bits start small startInside capacity order room binary covered fits mapped
  have chainCost := Nat.mul_le_mul_left (sizedProbePrice kind) bounded
  obtain ⟨paid, answer, target, paidBound, answerBound, run, frame⟩ := sized_chain_execute source p kind _ length chain keyLength queryFits
    source locals rfl rfl rfl queryMapped code (Nat.le_trans chainCost enough)
  exact ⟨paid, answer, target, Nat.le_trans paidBound chainCost, answerBound, run, frame⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.sized_chain_of_prefix
#print axioms InitECandidate.Solver.MutableTable.Find.sized_chain_of_order
#print axioms InitECandidate.Solver.MutableTable.Find.sized_scan_count_bound
