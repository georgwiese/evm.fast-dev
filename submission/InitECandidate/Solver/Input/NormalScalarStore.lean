import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Normal execution of an actual scalar local-to-field store derives its
base-word read, destination mapping and exact stored word. -/
theorem scalar_store_normal {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (baseName valueName : String) (offset word : BitVec 64)
    (stored : source.locals.lookup (ofString valueName) = some (.val (.word word)))
    (run : evaluateHOLFiniteState source (.store (addConst (localVar baseName) offset) (localVar valueName)) = (none, post)) :
    ∃ base : BitVec 64,
      source.locals.lookup (ofString baseName) = some (.val (.word base)) ∧
      source.memaddrs (base + offset) ∧
      post = {source with memory := WitnessRadix.StoreWord.put source.memory (base + offset) word} ∧
      post.memory (base + offset) = .word word := by
  classical
  cases baseRead : source.locals.lookup (ofString baseName) with
  | none =>
    simp [evaluateHOLFiniteState_store, addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, baseRead] at run
  | some value =>
    cases value with
    | rStruct fields =>
      simp [evaluateHOLFiniteState_store, addConst, localVar, evalHOLExact, evalListHOLExact,
        toExact, baseRead, valueIsWord] at run
    | nStruct name fields =>
      simp [evaluateHOLFiniteState_store, addConst, localVar, evalHOLExact, evalListHOLExact,
        toExact, baseRead, valueIsWord] at run
    | val payload =>
      cases payload with
      | word base =>
        have addressRead : eval source (addConst (localVar baseName) offset) = some (.val (.word (base + offset))) := by
          simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, baseRead,
            valueIsWord, valueWord, wordOpHOL, wordOp]
        have valueRead : eval source (localVar valueName) = some (.val (.word word)) := by
          simpa only [eval, localVar, evalHOLExact, toExact] using stored
        by_cases mapped : source.memaddrs (base + offset)
        · have actual := WitnessRadix.StoreWord.execute source (addConst (localVar baseName) offset)
            (localVar valueName) (base + offset) word addressRead valueRead mapped
          have postEq : post = {source with memory := WitnessRadix.StoreWord.put source.memory (base + offset) word} := by
            rw [actual] at run
            exact (congrArg Prod.snd run).symm
          refine ⟨base, rfl, mapped, postEq, ?_⟩
          rw [postEq]
          simp [WitnessRadix.StoreWord.put]
        · simp only [eval] at addressRead valueRead
          rw [evaluateHOLFiniteState_store, addressRead, valueRead] at run
          simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, mapped] at run

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.scalar_store_normal
