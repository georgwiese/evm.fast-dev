import InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
import InitECandidate.Solver.Input.Witness.Fields

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real witness pointer/count stores preserve the shared input, heap
and payload gas facts. Both destination fields lie in the earlier si record. -/
theorem Context.pair_stores (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord array count : BitVec 64) (length offset : Nat) (name : String)
    (context : Context input source pointer statelessRecord record gasWord length)
    (inside : offset + 16 ≤ 96) (aligned : offset % 8 = 0)
    (tuple : source.locals.lookup (ofString name) = some (VarList.pairValue array count.toNat)) :
    Context input (Witness.pairStored source statelessRecord offset array count) pointer statelessRecord record gasWord length := by
  have firstRead : eval source (.rfield 0 (localVar name)) = some (.val (.word array)) := by
    simp [eval, localVar, VarList.pairValue, evalHOLExact, toExact, tuple]
  obtain ⟨firstRun, firstContext⟩ := context.stateless_store input source pointer statelessRecord record gasWord length offset
    (.rfield 0 (localVar name)) array (by omega) aligned firstRead
  let first := {source with memory := WitnessRadix.StoreWord.put source.memory (statelessRecord + BitVec.ofNat 64 offset) array}
  have tupleSaved : first.locals.lookup (ofString name) = some (VarList.pairValue array count.toNat) := tuple
  have secondRead : eval first (.rfield 1 (localVar name)) = some (.val (.word count)) := by
    simp [eval, localVar, VarList.pairValue, evalHOLExact, toExact, tupleSaved, BitVec.setWidth_eq]
  obtain ⟨secondRun, secondContext⟩ := firstContext.stateless_store input first pointer statelessRecord record gasWord length (offset + 8)
    (.rfield 1 (localVar name)) count (by omega) (by omega) secondRead
  exact secondContext

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.pair_stores
