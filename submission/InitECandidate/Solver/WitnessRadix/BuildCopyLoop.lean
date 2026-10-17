import InitECandidate.Solver.WitnessRadix.BuildRows

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch BuildProgram

def copyLoop : ProgHOL 64 := .while condition copyBody

def copyState {F : Type} (source : PanSemStateFiniteExact 64 F) (src start : BitVec 64) :
    Nat → List (BitVec 64) → PanSemStateFiniteExact 64 F
  | _, [] => source
  | index, value :: rest =>
      copyState (bind { source with
          clock := source.clock - 1
          memory := StoreWord.put source.memory (row src start (BitVec.ofNat 64 index)) value }
        "i" (BitVec.ofNat 64 (index + 1))) src start (index + 1) rest

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index count : Nat)
    (small : count < 2 ^ 64) (ordered : index ≤ count)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count)))) :
    @evalHOLFinite 64 F _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) condition =
      some (.val (.word (if index < count then 1#64 else 0#64))) := by
  classical
  have indexSmall : index < 2 ^ 64 := by omega
  simp [condition, localVar, evalHOLFinite, evalHOLExact, toExact, indexLocal, countLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt indexSmall]

/-- Complete execution of the actual construction copy loop, with separated
arrays, mapped cells and an exact memory poststate. Every copied word pays
one source clock; no clock is required when the interval is empty. -/
theorem loop_execute {F : Type} (input : List (BitVec 64))
    (source : PanSemStateFiniteExact 64 F) (src dst start : BitVec 64) (index count : Nat)
    (small : count < 2 ^ 64) (size : index + input.length = count)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))))
    (rows : Rows source.memory source.memaddrs dst start index input)
    (mapped : ∀ i, index ≤ i → i < count → source.memaddrs (row src start (BitVec.ofNat 64 i)))
    (separate : ∀ i j, index ≤ i → i < count → index ≤ j → j < count →
      row dst start (BitVec.ofNat 64 j) ≠ row src start (BitVec.ofNat 64 i))
    (enough : input.length ≤ source.clock) :
    evaluateHOLFiniteState source copyLoop = (none, copyState source src start index input) := by
  classical
  induction input generalizing source index with
  | nil =>
      have same : index = count := by simpa using size
      subst index
      rw [copyLoop, evaluateHOLFiniteState_while_total,
        condition_read source count count small (by omega) indexLocal countLocal]
      simp [copyState]
  | cons value rest ih =>
      have active : index < count := by simp only [List.length_cons] at size; omega
      have nonzero : source.clock ≠ 0 := by simp only [List.length_cons] at enough; omega
      obtain ⟨readMapped, readWord, restRows⟩ := rows
      let entry := decClockHOLFinite source
      let next := (bind { entry with
          memory := StoreWord.put source.memory (row src start (BitVec.ofNat 64 index)) value }
        "i" (BitVec.ofNat 64 (index + 1)))
      have body := body_execute entry src dst start (BitVec.ofNat 64 index) value
        srcLocal dstLocal startLocal indexLocal (mapped index (by omega) active) readMapped readWord
      have nextIndex : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by
        exact BitVec.ofNat_add_ofNat index 1
      rw [nextIndex] at body
      have rows' : Rows next.memory next.memaddrs dst start (index + 1) rest := by
        apply rows_store_away source.memory source.memaddrs dst start
          (row src start (BitVec.ofNat 64 index)) value (index + 1) rest restRows
        intro offset bound
        apply separate index (index + 1 + offset) (by omega) active (by omega)
        simp only [List.length_cons] at size
        omega
      have names : ofString "i" ≠ ofString "src" ∧ ofString "i" ≠ ofString "dst" ∧
          ofString "i" ≠ ofString "start" ∧ ofString "i" ≠ ofString "count" := by decide
      have src' : next.locals.lookup (ofString "src") = some (.val (.word src)) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, names.1, srcLocal]
      have dst' : next.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, names.2.1, dstLocal]
      have start' : next.locals.lookup (ofString "start") = some (.val (.word start)) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, names.2.2.1, startLocal]
      have count' : next.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))) := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite,
          HolFiniteMapExact.update, FUPDATE, names.2.2.2, countLocal]
      have index' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
        simp [next, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      have tailRun := ih next (index + 1) (by simp only [List.length_cons] at size; omega)
        src' dst' start' index' count' rows' (by intro i lo hi; exact mapped i (by omega) hi)
        (by intro i j ilo ihi jlo jhi; exact separate i j (by omega) ihi (by omega) jhi)
        (by change rest.length ≤ source.clock - 1; simp only [List.length_cons] at enough; omega)
      have body' : evaluateHOLFiniteState (decClockHOLFinite source) copyBody = (none, next) := body
      rw [copyLoop, evaluateHOLFiniteState_while_total,
        condition_read source index count small (by omega) indexLocal countLocal]
      simp only [if_pos active]
      rw [if_pos (by decide)]
      simp only [if_neg nonzero, body']
      have fixed : fixClockHOLFinite entry ((none : Option (PanSemResultExact 64)), next) =
          (none, next) := by simp [fixClockHOLFinite, next, QueryBranch.bind, setVarHOLFinite]
      change (let output := fixClockHOLFinite entry (none, next);
        evaluateHOLFiniteState output.2 copyLoop) = _
      simp only [fixed]
      exact tailRun

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.loop_execute
