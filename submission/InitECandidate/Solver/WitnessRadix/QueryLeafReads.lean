import InitECandidate.Solver.WitnessRadix.QueryLeaf

namespace InitECandidate.Solver.WitnessRadix.QueryLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem read_ordinal {F : Type} (source : PanSemStateFiniteExact 64 F)
    (ordinal : Nat) (small : ordinal < 2 ^ 63)
    (node : source.locals.lookup (ofString "node") = some (.val (.word (WordBits.leafTag ordinal)))) :
    eval source ordinalExpression = some (.val (.word (BitVec.ofNat 64 ordinal))) := by
  classical
  have decoded := WordBits.leafTag_decode ordinal small
  simp [eval, ordinalExpression, localVar, evalHOLExact, toExact, node,
    valueIsWord, valueWord, wordShiftHOL, decoded]

theorem read_keys {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys : BitVec 64)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (mapped : source.memaddrs (table + 32#64))
    (stored : source.memory (table + 32#64) = .word keys) :
    eval source keysExpression = some (.val (.word keys)) := by
  classical
  simp [eval, keysExpression, localVar, addConst, evalHOLExact, evalListHOLExact,
    toExact, db, isWfShapeExactHOL, memLoadHOLExact, mapped, stored,
    valueIsWord, valueWord, wordOpHOL, wordOp]

theorem read_arguments {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys ordinal hash : BitVec 64)
    (keyLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash))) :
    evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (Memeq32.values (keys + ordinal * 32#64) hash) := by
  classical
  simp [arguments, Memeq32.values, localVar, evalListHOLFinite, evalHOLFinite,
    evalHOLExact, evalListHOLExact, toExact, keyLocal, ordinalLocal, hashLocal,
    valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

theorem read_record {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table vals ordinal record : BitVec 64)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (headerMapped : source.memaddrs (table + 40#64))
    (headerWord : source.memory (table + 40#64) = .word vals)
    (recordMapped : source.memaddrs (vals + ordinal * 8#64))
    (recordWord : source.memory (vals + ordinal * 8#64) = .word record) :
    eval source recordExpression = some (.val (.word record)) := by
  classical
  simp [eval, recordExpression, localVar, addConst, evalHOLExact, evalListHOLExact,
    toExact, db, ordinalLocal, isWfShapeExactHOL, memLoadHOLExact, headerMapped,
    headerWord, recordMapped, recordWord, valueIsWord, valueWord, panOpHOL,
    wordOpHOL, wordOp]

end InitECandidate.Solver.WitnessRadix.QueryLeaf

#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.read_ordinal
#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.read_arguments
#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.read_record
