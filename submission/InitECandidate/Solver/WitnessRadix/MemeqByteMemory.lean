import InitECandidate.Solver.WitnessRadix.MemeqByteKeys

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem indexed_byte {F : Type} (state : PanSemStateFiniteExact 64 F)
    (clock index : Nat) (address : BitVec 64) :
    @panMemLoadByteHOL 64 _ (indexed state clock index).memory (indexed state clock index).memaddrs
      (fun pointer => Classical.propDecidable ((indexed state clock index).memaddrs pointer))
      (indexed state clock index).be address =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun pointer => Classical.propDecidable (state.memaddrs pointer)) state.be address := by
  classical
  by_cases mapped : state.memaddrs (panByteAlignHOL (width := 64) address)
  all_goals simp [indexed, QueryBranch.bind, setVarHOLFinite, panMemLoadByteHOL, mapped]

theorem byteChecks_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b index : BitVec 64) (left right : Fin 8 → BitVec 8)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (current : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (leftLoaded : ∀ offset : Fin 8, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (a + index + BitVec.ofNat 64 offset.val) = some (toUInt8 (left offset)))
    (rightLoaded : ∀ offset : Fin 8, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (b + index + BitVec.ofNat 64 offset.val) = some (toUInt8 (right offset))) :
    ∀ check ∈ byteChecks (fun i => (left i).setWidth 64) (fun i => (right i).setWidth 64),
      CompareChain.Ready state check := by
  have l (i : Fin 8) : eval state (byteAt "a" i.val) = some (.val (.word ((left i).setWidth 64))) := by
    rw [← widened_byte (left i)]
    exact eval_byteAt state "a" a index i.val (toUInt8 (left i)) argA current (leftLoaded i)
  have r (i : Fin 8) : eval state (byteAt "b" i.val) = some (.val (.word ((right i).setWidth 64))) := by
    rw [← widened_byte (right i)]
    exact eval_byteAt state "b" b index i.val (toUInt8 (right i)) argB current (rightLoaded i)
  intro check member
  simp only [byteChecks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨l 0, r 0⟩
  · exact ⟨l 1, r 1⟩
  · exact ⟨l 2, r 2⟩
  · exact ⟨l 3, r 3⟩
  · exact ⟨l 4, r 4⟩
  · exact ⟨l 5, r 5⟩
  · exact ⟨l 6, r 6⟩
  · exact ⟨l 7, r 7⟩

/-- All loop-load premises follow from just the original two 32-byte memory
views. Clock updates and the local i binding do not change any byte load. -/
theorem byte_loop_ready_of_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (left right : ByteKeys.Key)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (leftLoaded : ∀ byte : Fin 32, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (a + BitVec.ofNat 64 byte.val) = some (toUInt8 (left byte)))
    (rightLoaded : ∀ byte : Fin 32, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (b + BitVec.ofNat 64 byte.val) = some (toUInt8 (right byte))) :
    ByteLoopReady state (chunks left) (chunks right) := by
  intro start inside clock
  let block : Fin 4 := ⟨start, inside⟩
  have encoded : Fin.ofNat 4 start = block := by
    apply Fin.ext
    change start % 4 = start
    exact Nat.mod_eq_of_lt inside
  rw [encoded]
  have argA' : (indexed state clock (8 * start)).locals.lookup (ofString "a") = some (.val (.word a)) := by
    have different : ofString "i" ≠ ofString "a" := by decide
    simp [indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, argA]
  have argB' : (indexed state clock (8 * start)).locals.lookup (ofString "b") = some (.val (.word b)) := by
    have different : ofString "i" ≠ ofString "b" := by decide
    simp [indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, argB]
  apply byteChecks_ready (indexed state clock (8 * start)) a b (BitVec.ofNat 64 (8 * start))
    (fun offset => left ⟨8 * start + offset.val, by have := offset.isLt; omega⟩)
    (fun offset => right ⟨8 * start + offset.val, by have := offset.isLt; omega⟩)
    argA' argB' (indexed_current state clock (8 * start))
  · intro offset
    rw [indexed_byte]
    have read := leftLoaded ⟨8 * start + offset.val, by have := offset.isLt; omega⟩
    have address : a + BitVec.ofNat 64 (8 * start + offset.val) =
        a + BitVec.ofNat 64 (8 * start) + BitVec.ofNat 64 offset.val := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address] at read
    exact read
  · intro offset
    rw [indexed_byte]
    have read := rightLoaded ⟨8 * start + offset.val, by have := offset.isLt; omega⟩
    have address : b + BitVec.ofNat 64 (8 * start + offset.val) =
        b + BitVec.ofNat 64 (8 * start) + BitVec.ofNat 64 offset.val := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [address] at read
    exact read

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byteChecks_ready
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.byte_loop_ready_of_memory
