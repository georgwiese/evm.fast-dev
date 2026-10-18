import InitECandidate.Solver.GasBudget.JournalDeleteGuard
import InitECandidate.Solver.GasBudget.JournalZone
import InitECandidate.Solver.WitnessRadix.AllocationNormalExpected
import InitECandidate.Solver.WitnessRadix.CopyNormalCall

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def lengthExpression : ExpHOL 64 := .load .one (addConst (localVar "t") 0#64)
def copyCall : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [localVar "kc", localVar "key", localVar "klen"]
def keyProgram (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "klen") .one lengthExpression
    (.decCall (ofString "kc") .one (ofString "alloc") [localVar "klen"] (.seq copyCall continuation))
def setAfterCopy : ProgHOL 64 := match setAfterGuard with | .dec _ _ _ (.decCall _ _ _ _ (.seq _ rest)) => rest | _ => .skip
def deleteAfterCopy : ProgHOL 64 := match deleteAfterGuard with | .dec _ _ _ (.decCall _ _ _ _ (.seq _ rest)) => rest | _ => .skip

theorem set_key_shape : setAfterGuard = keyProgram setAfterCopy := by
  simp only [setAfterGuard, setAfterGet, setBody, setAfterCopy, Guest.guestFn_jset, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, keyProgram, lengthExpression, copyCall, localVar, addConst]

theorem delete_key_shape : deleteAfterGuard = keyProgram deleteAfterCopy := by
  simp only [deleteAfterGuard, deleteAfterEmpty, deleteAfterGet, deleteBody, deleteAfterCopy, Guest.guestFn_jdel, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, keyProgram, lengthExpression, copyCall, localVar, addConst]

theorem length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : NaturalLayout.Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (NaturalLayout.cell plan .header 0)))) :
    eval source lengthExpression = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))) := by
  have mapped : source.memaddrs (NaturalLayout.cell plan .header 0) := by
    rw [domain]
    exact NaturalLayout.mapped kind plan table.valid .header 0 (by change 0 < 72; decide) (by decide)
  have stored : source.memory (NaturalLayout.cell plan .header 0) = .word (BitVec.ofNat 64 (KeyHash.keySize kind)) :=
    table.header 0 _ (by simp [MemoryModel.headerEntries])
  simp [eval, lengthExpression, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, tableLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, isWfShapeExactHOL, memLoadHOLExact, mapped, stored]

theorem key_rounding (kind : KeyHash.Kind) :
    KeyHash.keySize kind ≤ NaturalLayout.stride kind ∧ NaturalLayout.stride kind < KeyHash.keySize kind + 8 ∧
      NaturalLayout.stride kind % 8 = 0 ∧ KeyHash.keySize kind + 32 < 2 ^ 64 := by
  cases kind <;> decide

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_key_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_key_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.length_read
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_rounding
