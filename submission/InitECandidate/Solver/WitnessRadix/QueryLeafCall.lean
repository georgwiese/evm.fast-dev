import InitECandidate.Solver.WitnessRadix.QueryLeafReads

namespace InitECandidate.Solver.WitnessRadix.QueryLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

def comparisonCall : ProgHOL 64 :=
  .decCall (ofString "equal") .one (ofString "memeq") arguments afterCompare

/-- The actual leaf comparison call and both return paths, from concrete
memory and code facts. Erasing locals exposes that all other fields are
preserved except for at most five source clocks. -/
theorem comparison_return {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals ordinal hash record pointer length : BitVec 64)
    (left right : ByteKeys.Key)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (leftView : MemoryBytes.ByteView source (keys + ordinal * 32#64) left)
    (rightView : MemoryBytes.ByteView source hash right)
    (leftFits : (keys + ordinal * 32#64).toNat + 32 < 2 ^ 64)
    (rightFits : hash.toNat + 32 < 2 ^ 64)
    (little : source.be = false) (enough : 5 ≤ source.clock)
    (headerMapped : source.memaddrs (table + 40#64))
    (headerWord : source.memory (table + 40#64) = .word vals)
    (recordMapped : source.memaddrs (vals + ordinal * 8#64))
    (recordWord : source.memory (vals + ordinal * 8#64) = .word record)
    (pointerMapped : source.memaddrs record) (lengthMapped : source.memaddrs (record + 8#64))
    (pointerWord : source.memory record = .word pointer)
    (lengthWord : source.memory (record + 8#64) = .word length) :
    ∃ paid, paid ≤ 4 ∧
      (evaluateHOLFiniteState source comparisonCall).1 =
        some (.returned (if left = right then found pointer length else QueryEmpty.zeros)) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source comparisonCall).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - (paid + 1) } := by
  classical
  obtain ⟨callee, lookup, argA, argB, argN, _⟩ :=
    Memeq32.environment source.code.lookup (keys + ordinal * 32#64) hash code
  obtain ⟨paid, bound, execution⟩ := Memeq32.call_execute source callee arguments afterCompare
    (keys + ordinal * 32#64) hash left right
    (read_arguments source keys ordinal hash keyLocal ordinalLocal hashLocal)
    lookup argA argB argN leftView rightView leftFits rightFits little enough
  let compared := bind { source with clock := source.clock - (paid + 1) } "equal"
    (if left = right then 1#64 else 0#64)
  have eqDb : ofString "db" ≠ ofString "equal" := by decide
  have eqOrdinal : ofString "ordinal" ≠ ofString "equal" := by decide
  have db' : compared.locals.lookup (ofString "db") = some (.val (.word table)) := by
    simp [compared, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      eqDb, Ne.symm eqDb, db]
  have ordinal' : compared.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)) := by
    simp [compared, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      eqOrdinal, Ne.symm eqOrdinal, ordinalLocal]
  have equal' : compared.locals.lookup (ofString "equal") =
      some (.val (.word (if left = right then 1#64 else 0#64))) := by
    simp [compared, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have readRecord := read_record compared table vals ordinal record db' ordinal'
    headerMapped headerWord recordMapped recordWord
  change evaluateHOLFiniteState source comparisonCall = _ at execution
  refine ⟨paid, bound, ?_, ?_⟩
  all_goals rw [execution]
  · change (evaluateHOLFiniteState compared afterCompare).1 = _
    by_cases same : left = right
    · have returned := after_hit compared record pointer length (by simpa [same] using equal')
        readRecord pointerMapped lengthMapped pointerWord lengthWord
      rw [returned, if_pos same]
    · have returned := after_miss compared (by simpa [same] using equal')
      rw [returned, if_neg same]
  · change emptyLocalsHOLFinite (restore source "equal"
      (evaluateHOLFiniteState compared afterCompare).2) = _
    by_cases same : left = right
    · have returned := after_hit compared record pointer length (by simpa [same] using equal')
        readRecord pointerMapped lengthMapped pointerWord lengthWord
      rw [returned]
      rfl
    · have returned := after_miss compared (by simpa [same] using equal')
      rw [returned]
      rfl

end InitECandidate.Solver.WitnessRadix.QueryLeaf

#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.comparison_return
