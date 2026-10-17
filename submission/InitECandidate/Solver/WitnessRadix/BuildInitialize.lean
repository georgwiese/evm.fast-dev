import InitECandidate.Solver.WitnessRadix.BuildEntry

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

structure Header {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals src dst : BitVec 64) : Prop where
  keysMapped : source.memaddrs (table + 32#64)
  keysWord : source.memory (table + 32#64) = .word keys
  valsMapped : source.memaddrs (table + 40#64)
  valsWord : source.memory (table + 40#64) = .word vals
  srcMapped : source.memaddrs (table + 56#64)
  srcWord : source.memory (table + 56#64) = .word src
  dstMapped : source.memaddrs (table + 64#64)
  dstWord : source.memory (table + 64#64) = .word dst

def initialValues (table count keys vals src dst : BitVec 64) : List (String × BitVec 64) :=
  [("keys", keys), ("vals", vals), ("src", src), ("dst", dst),
   ("pending_start", src + count * 8#64), ("pending_count", dst + count * 8#64),
   ("pending_node", vals + count * 8#64), ("node_next", keys + count * 32#64),
   ("dest", table + 24#64), ("start", 0#64), ("count", count), ("bit", 0#64), ("depth", 0#64)]

def entered {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64) : PanSemStateFiniteExact 64 F :=
  (initialValues table count keys vals src dst).foldl (fun state pair => bind state pair.1 pair.2) source

/-- All thirteen literal prefix declarations are justified by the actual ABI
and four actual header cells. No prefix execution is assumed. -/
theorem initialize_entry {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word count)))
    (cells : Header source table keys vals src dst) :
    ∃ restoreStack, Initializes source bindings (entered source table count keys vals src dst) restoreStack := by
  classical
  simp [ofString] at tableLocal countLocal
  refine ⟨_, .step keys ?_ (.step vals ?_ (.step src ?_ (.step dst ?_
    (.step (src + count * 8#64) ?_ (.step (dst + count * 8#64) ?_
    (.step (vals + count * 8#64) ?_ (.step (keys + count * 32#64) ?_
    (.step (table + 24#64) ?_ (.step 0#64 ?_ (.step count ?_ (.step 0#64 ?_ (.step 0#64 ?_ (.done _)))))))))))))⟩
  all_goals simp [eval, header, suffix, multiply, localVar, addConst, evalHOLExact,
    evalListHOLExact, toExact, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, ofString, tableLocal, countLocal,
    isWfShapeExactHOL, memLoadHOLExact, cells.keysMapped, cells.keysWord,
    cells.valsMapped, cells.valsWord, cells.srcMapped, cells.srcWord,
    cells.dstMapped, cells.dstWord, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

theorem prefix_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word count)))
    (cells : Header source table keys vals src dst) :
    ∃ restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F,
      (∀ output, emptyLocalsHOLFinite (restoreStack output) = emptyLocalsHOLFinite output) ∧
      evaluateHOLFiniteState source BuildProgram.body =
        (let output := evaluateHOLFiniteState (entered source table count keys vals src dst) core;
         (output.1, restoreStack output.2)) := by
  obtain ⟨restoreStack, setup⟩ := initialize_entry source table count keys vals src dst tableLocal countLocal cells
  exact ⟨restoreStack, restoration_frame setup, by rw [body_shape]; exact declarations_execute setup core⟩

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.initialize_entry
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.prefix_execute
