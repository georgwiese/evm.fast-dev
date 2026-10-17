import InitECandidate.Solver.WitnessRadix.TableNewProgram

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

def headerActions : List Action :=
  [.command (headerStore 0#64 (localVar "key_len")),
   .command (headerStore 8#64 (localVar "stride")),
   .command (headerStore 16#64 (localVar "cap")),
   .command (headerStore 24#64 (.const 0#64))]

def headerWrites (table capacity : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(table, 32#64), (table + 8#64, 32#64), (table + 16#64, capacity), (table + 24#64, 0#64)]

def headerState {F : Type} (source : PanSemStateFiniteExact 64 F) (table capacity : BitVec 64) : PanSemStateFiniteExact 64 F :=
  { source with memory := WordWrites.write source.memory (headerWrites table capacity) }

theorem header_store {F : Type} (source : PanSemStateFiniteExact 64 F) (table offset value : BitVec 64) (expression : ExpHOL 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (read : eval source expression = some (.val (.word value))) (mapped : source.memaddrs (table + offset)) :
    evaluateHOLFiniteState source (headerStore offset expression) =
      (none, { source with memory := StoreWord.put source.memory (table + offset) value }) := by
  apply StoreWord.execute
  · simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, tableLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  · exact read
  · exact mapped

/-- Four literal header stores establish key length, stride, capacity and
zero count. They cost no source clocks and preserve every other field. -/
theorem header_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (table capacity : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word 32#64)))
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word 32#64)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (mapped : ∀ field : Fin 4, source.memaddrs (table + BitVec.ofNat 64 (8 * field.val))) :
    Executes source headerActions (headerState source table capacity) id := by
  let first := { source with memory := StoreWord.put source.memory table 32#64 }
  let second := { first with memory := StoreWord.put first.memory (table + 8#64) 32#64 }
  let third := { second with memory := StoreWord.put second.memory (table + 16#64) capacity }
  have firstRun := header_store source table 0#64 32#64 (localVar "key_len") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, keyLocal]) (mapped 0)
  have secondRun := header_store first table 8#64 32#64 (localVar "stride") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, first, strideLocal]) (mapped 1)
  have thirdRun := header_store second table 16#64 capacity (localVar "cap") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, second, first, capLocal]) (mapped 2)
  have fourthRun := header_store third table 24#64 0#64 (.const 0#64) tableLocal rfl
    (mapped (⟨3, by decide⟩ : Fin 4))
  have firstRun' : evaluateHOLFiniteState source (headerStore 0#64 (localVar "key_len")) = (none, first) := by
    simpa only [BitVec.add_zero] using firstRun
  change evaluateHOLFiniteState third (headerStore 24#64 (.const 0#64)) =
    (none, headerState source table capacity) at fourthRun
  exact .command firstRun' (Nat.le_refl _) (.command secondRun (Nat.le_refl _)
    (.command thirdRun (Nat.le_refl _) (.command fourthRun (Nat.le_refl _) (.done _))))

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.header_executes
