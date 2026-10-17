import InitECandidate.Solver.WitnessRadix.MemeqByteMemory

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

/-- The entire fixed-source comparator on unaligned 32-byte keys, from the
actual 64 byte-load results and ABI bindings. At most four source clock units
are consumed, all memory/FFI fields are preserved, and temporary i is restored. -/
theorem unaligned_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (left right : ByteKeys.Key)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (unaligned : (a ||| b) &&& 7#64 ≠ 0#64)
    (leftLoaded : ∀ byte : Fin 32, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (a + BitVec.ofNat 64 byte.val) = some (toUInt8 (left byte)))
    (rightLoaded : ∀ byte : Fin 32, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (b + BitVec.ofNat 64 byte.val) = some (toUInt8 (right byte)))
    (enough : 4 ≤ state.clock) :
    ∃ paid, paid ≤ 4 ∧ evaluateHOLFiniteState state body =
      (some (.returned (.val (.word (if left = right then 1#64 else 0#64)))),
        restore state "i" (emptyLocalsHOLFinite { state with clock := state.clock - paid })) := by
  classical
  let initial := indexed state state.clock 0
  have iNotA : ofString "i" ≠ ofString "a" := by decide
  have iNotB : ofString "i" ≠ ofString "b" := by decide
  have argA' : initial.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simp [initial, indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, iNotA, argA]
  have argB' : initial.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [initial, indexed, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, iNotB, argB]
  have alignment := alignment_eval_not initial a b argA' argB' unaligned
  have ready := byte_loop_ready_of_memory state a b left right argA argB leftLoaded rightLoaded
  obtain ⟨paid, bound, run⟩ := unaligned_execute state (chunks left) (chunks right) length alignment ready enough
  have bitEq : (if allBlocks (chunks left) (chunks right) 0 4 then 1#64 else 0#64) =
      if left = right then 1#64 else 0#64 := by
    by_cases same : left = right
    · have accepted := (allBytes_agree_iff left right).mpr same
      rw [if_pos accepted, if_pos same]
    · have rejected : allBlocks (chunks left) (chunks right) 0 4 = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        exact same ((allBytes_agree_iff left right).mp accepted)
      simp [same, rejected]
  rw [bitEq] at run
  exact ⟨paid, bound, run⟩

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.unaligned_memory
