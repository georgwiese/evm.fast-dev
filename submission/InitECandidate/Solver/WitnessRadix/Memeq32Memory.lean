import InitECandidate.Solver.WitnessRadix.Memeq32Entry
import InitECandidate.Solver.WitnessRadix.WordKeys

namespace InitECandidate.Solver.WitnessRadix.Memeq32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

private theorem opAnd (left right : BitVec 64) :
    wordOpHOL .and [left, right] = some (left &&& right) := by
  change some (left &&& (right &&& ~~~(0#64))) = _
  rw [BitVec.not_zero, BitVec.and_allOnes]

private theorem opOr (left right : BitVec 64) :
    wordOpHOL .or [left, right] = some (left ||| right) := by
  change some (left ||| (right ||| 0#64)) = _
  rw [BitVec.or_zero]

theorem alignment_eval {F : Type} (state : PanSemStateFiniteExact 64 F) (left right : BitVec 64)
    (a : state.locals.lookup (ofString "a") = some (.val (.word left)))
    (b : state.locals.lookup (ofString "b") = some (.val (.word right)))
    (aligned : (left ||| right) &&& 7#64 = 0#64) :
    eval state alignmentTest = some (.val (.word 1#64)) := by
  classical
  simp only [eval, alignmentTest, localVar, evalHOLExact, evalListHOLExact, toExact,
    a, b, valueIsWord, valueWord, List.all_cons, List.all_nil, Bool.and_self,
    List.map_cons, List.map_nil, opOr, opAnd, Option.map_some, ↓reduceIte,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, aligned, beq_self_eq_true]
  rfl

theorem alignment_eval_not {F : Type} (state : PanSemStateFiniteExact 64 F) (left right : BitVec 64)
    (a : state.locals.lookup (ofString "a") = some (.val (.word left)))
    (b : state.locals.lookup (ofString "b") = some (.val (.word right)))
    (unaligned : (left ||| right) &&& 7#64 ≠ 0#64) :
    eval state alignmentTest = some (.val (.word 0#64)) := by
  classical
  have mask : ((left ||| right) &&& 7#64 == 0#64) = false := beq_eq_false_iff_ne.mpr unaligned
  simp only [eval, alignmentTest, localVar, evalHOLExact, evalListHOLExact, toExact,
    a, b, valueIsWord, valueWord, List.all_cons, List.all_nil, Bool.and_self,
    List.map_cons, List.map_nil, opOr, opAnd, Option.map_some, ↓reduceIte,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, mask, Bool.false_eq_true]
  rfl

theorem ready_of_words {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (left right : Fin 4 → BitVec 64)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (leftMapped : ∀ i : Fin 4, state.memaddrs (a + BitVec.ofNat 64 (8 * i.val)))
    (rightMapped : ∀ i : Fin 4, state.memaddrs (b + BitVec.ofNat 64 (8 * i.val)))
    (leftWords : ∀ i : Fin 4, state.memory (a + BitVec.ofNat 64 (8 * i.val)) = .word (left i))
    (rightWords : ∀ i : Fin 4, state.memory (b + BitVec.ofNat 64 (8 * i.val)) = .word (right i)) :
    ∀ check ∈ checks left right, CompareChain.Ready state check := by
  have l (i : Fin 4) := eval_wordAt state "a" a (left i) (8 * i.val) argA (leftMapped i) (leftWords i)
  have r (i : Fin 4) := eval_wordAt state "b" b (right i) (8 * i.val) argB (rightMapped i) (rightWords i)
  intro check member
  simp only [checks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨l 0, r 0⟩
  · exact ⟨l 1, r 1⟩
  · exact ⟨l 2, r 2⟩
  · exact ⟨l 3, r 3⟩

theorem agrees_iff_keys (left right : Fin 4 → BitVec 64) :
    CompareChain.agrees (checks left right) = true ↔ WordKeys.key left = WordKeys.key right := by
  rw [WordKeys.equal_iff]
  simp only [CompareChain.agrees, checks, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => exact h0
    | succ i => cases i with
      | zero => exact h1
      | succ i => cases i with
        | zero => exact h2
        | succ i => cases i with
          | zero => exact h3
          | succ i => omega
  · intro same
    subst right
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Full fixed-source execution from actual argument bindings, mapped words
and the alignment mask. The compared byte keys are the little-endian bytes
of those four loaded words, rather than an assumed memeq oracle result. -/
theorem aligned_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (left right : Fin 4 → BitVec 64)
    (argA : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (argB : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (length : state.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (aligned : (a ||| b) &&& 7#64 = 0#64)
    (leftMapped : ∀ i : Fin 4, state.memaddrs (a + BitVec.ofNat 64 (8 * i.val)))
    (rightMapped : ∀ i : Fin 4, state.memaddrs (b + BitVec.ofNat 64 (8 * i.val)))
    (leftWords : ∀ i : Fin 4, state.memory (a + BitVec.ofNat 64 (8 * i.val)) = .word (left i))
    (rightWords : ∀ i : Fin 4, state.memory (b + BitVec.ofNat 64 (8 * i.val)) = .word (right i)) :
    evaluateHOLFiniteState state body =
      (some (.returned (.val (.word (if WordKeys.key left = WordKeys.key right then 1#64 else 0#64)))),
        restore state "i" (emptyLocalsHOLFinite (bind state "i" 0#64))) := by
  classical
  let loaded := bind state "i" 0#64
  have iNotA : ofString "i" ≠ ofString "a" := by decide
  have iNotB : ofString "i" ≠ ofString "b" := by decide
  have argA' : loaded.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simp [loaded, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, iNotA, argA]
  have argB' : loaded.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simp [loaded, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, iNotB, argB]
  have ready := ready_of_words loaded a b left right argA' argB' leftMapped rightMapped leftWords rightWords
  have run := aligned_execute state left right length (alignment_eval loaded a b argA' argB' aligned) ready
  have bitEq : (if CompareChain.agrees (checks left right) then 1#64 else 0#64) =
      if WordKeys.key left = WordKeys.key right then 1#64 else 0#64 := by
    by_cases equal : WordKeys.key left = WordKeys.key right
    · have accepted := (agrees_iff_keys left right).mpr equal
      simp [equal, accepted]
    · have rejected : CompareChain.agrees (checks left right) = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        exact equal ((agrees_iff_keys left right).mp accepted)
      simp [equal, rejected]
  rw [bitEq] at run
  exact run

end InitECandidate.Solver.WitnessRadix.Memeq32

#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.alignment_eval
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.alignment_eval_not
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.ready_of_words
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.agrees_iff_keys
#print axioms InitECandidate.Solver.WitnessRadix.Memeq32.aligned_memory
