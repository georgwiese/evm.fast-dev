import InitECandidate.Solver.WitnessRadix.TableHeader
import InitECandidate.Solver.MutableTable.NaturalLayoutFresh

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix WitnessRadix

def headerWrites (kind : KeyHash.Kind) (table capacity : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(table, BitVec.ofNat 64 (KeyHash.keySize kind)), (table + 8#64, BitVec.ofNat 64 (NaturalLayout.stride kind)), (table + 16#64, capacity), (table + 24#64, 0#64)]

def headerState {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table capacity : BitVec 64) : PanSemStateFiniteExact 64 F :=
  { source with memory := WordWrites.write source.memory (headerWrites kind table capacity) }

/-- Four literal header stores establish key length, stride, capacity and
zero count. They cost no source clocks and preserve every other field. -/
theorem header_executes {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (table capacity : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) )
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (NaturalLayout.stride kind)))) )
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (mapped : ∀ field : Fin 4, source.memaddrs (table + BitVec.ofNat 64 (8 * field.val))) :
    Executes source TableNew.headerActions (headerState source kind table capacity) id := by
  let first := { source with memory := StoreWord.put source.memory table (BitVec.ofNat 64 (KeyHash.keySize kind)) }
  let second := { first with memory := StoreWord.put first.memory (table + 8#64) (BitVec.ofNat 64 (NaturalLayout.stride kind)) }
  let third := { second with memory := StoreWord.put second.memory (table + 16#64) capacity }
  have firstRun := TableNew.header_store source table 0#64 (BitVec.ofNat 64 (KeyHash.keySize kind)) (localVar "key_len") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, keyLocal]) (mapped 0)
  have secondRun := TableNew.header_store first table 8#64 (BitVec.ofNat 64 (NaturalLayout.stride kind)) (localVar "stride") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, first, strideLocal]) (mapped 1)
  have thirdRun := TableNew.header_store second table 16#64 capacity (localVar "cap") tableLocal
    (by simp [eval, localVar, evalHOLExact, toExact, second, first, capLocal]) (mapped 2)
  have fourthRun := TableNew.header_store third table 24#64 0#64 (.const 0#64) tableLocal rfl
    (mapped (⟨3, by decide⟩ : Fin 4))
  have firstRun' : evaluateHOLFiniteState source (TableNew.headerStore 0#64 (localVar "key_len")) = (none, first) := by
    simpa only [BitVec.add_zero] using firstRun
  change evaluateHOLFiniteState third (TableNew.headerStore 24#64 (.const 0#64)) =
    (none, headerState source kind table capacity) at fourthRun
  exact .command firstRun' (Nat.le_refl _) (.command secondRun (Nat.le_refl _)
    (.command thirdRun (Nat.le_refl _) (.command fourthRun (Nat.le_refl _) (.done _))))

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.header_executes
