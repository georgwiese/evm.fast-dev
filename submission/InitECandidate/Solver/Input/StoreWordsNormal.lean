import InitECandidate.Solver.Input.StoreNormal

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Invert the value read and all actual mapped writes of a normal store.
No value-expression success or output-memory oracle is an entry premise. -/
theorem store_at_normal {F : Type} (source target : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64) (address : BitVec 64)
    (read : eval source destination = some (.val (.word address)))
    (normal : evaluateHOLFiniteState source (.store destination expression) = (none, target)) :
    ∃ value memory, eval source expression = some value ∧
      @panMemStoresHOL 64 _ address (flattenHOL value) source.memaddrs (fun current => Classical.propDecidable (source.memaddrs current)) source.memory = some memory ∧
      target = {source with memory := memory} := by
  classical
  simp only [eval] at read
  rw [evaluateHOLFiniteState_store, read] at normal
  simp only at normal
  generalize evaluated : evalHOLExact source.toExact expression = output at normal
  cases output with
  | none => cases normal
  | some value =>
    simp only at normal
    generalize stored : panMemStoresHOL address (flattenHOL value) source.memaddrs source.memory = memoryOutput at normal
    cases memoryOutput with
    | none => cases normal
    | some memory =>
      have targetEq := congrArg Prod.snd normal
      exact ⟨value, memory, evaluated, stored, targetEq.symm⟩

/-- Exact full-word stores preserve all cells outside their actual finite
write list, including tuple stores. Addresses retain64bit wrapping semantics. -/
theorem words_away (values : List (HolWordLab 64)) (address query : BitVec 64) (domain : BitVec 64 → Prop) (memory output : BitVec 64 → HolWordLab 64)
    (normal : @panMemStoresHOL 64 _ address values domain (fun current => Classical.propDecidable (domain current)) memory = some output)
    (away : ∀ index < values.length, query ≠ address + BitVec.ofNat 64 (8 * index)) : output query = memory query := by
  classical
  induction values generalizing address memory with
  | nil =>
    simp only [panMemStoresHOL, Option.some.injEq] at normal
    rw [← normal]
  | cons value rest ih =>
    by_cases mapped : domain address
    · simp only [panMemStoresHOL, panMemStoreHOL, if_pos mapped] at normal
      have following : ∀ index < rest.length, query ≠ address + panBytesInWord 64 + BitVec.ofNat 64 (8 * index) := by
        intro index inside
        have next := away (index + 1) (by simp only [List.length_cons]; omega)
        have same : address + panBytesInWord 64 + BitVec.ofNat 64 (8 * index) = address + BitVec.ofNat 64 (8 * (index + 1)) := by
          simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
          change address + 8#64 + BitVec.ofNat 64 (8 * index) = address + (BitVec.ofNat 64 (8 * index) + 8#64)
          rw [BitVec.add_assoc, BitVec.add_comm (8#64 : BitVec 64)]
        rw [same]
        exact next
      have preserved := ih (address + panBytesInWord 64) (fun current => if current = address then value else memory current) normal following
      have first : query ≠ address := by simpa only [Nat.mul_zero, BitVec.add_zero] using away 0 (by simp)
      simpa only [if_neg first] using preserved
    · simp only [panMemStoresHOL, panMemStoreHOL, if_neg mapped] at normal
      cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.store_at_normal
#print axioms InitECandidate.Solver.Input.words_away
