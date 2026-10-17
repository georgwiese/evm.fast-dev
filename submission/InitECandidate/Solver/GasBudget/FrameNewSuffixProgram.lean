import InitECandidate.Solver.GasBudget.FrameNewFields
import InitECandidate.Solver.GasBudget.TableCount

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def messageLoad (offset : Nat) : ExpHOL 64 := .load .one (addConst (localVar "msg") (BitVec.ofNat 64 offset))
def jumpFields (bitmap : BitVec 64) : List FieldStores.Field := [⟨80, .saved "jd" bitmap⟩]
def logFields (logs message : BitVec 64) : List FieldStores.Field :=
  [⟨88, .saved "logs" logs⟩, ⟨104, .literal 1#64⟩, ⟨112, .saved "msg" message⟩]
def deleteFields (table addresses keys : BitVec 64) : List FieldStores.Field :=
  [⟨136, .saved "del" table⟩, ⟨168, .copied 152 addresses⟩, ⟨176, .copied 160 keys⟩]
def firstCountFields (count : BitVec 64) : List FieldStores.Field := [⟨264, .saved "acc_n" count⟩]
def finalFields (count empty : BitVec 64) : List FieldStores.Field :=
  [⟨272, .saved "acc_n" count⟩, ⟨120, .globalSaved "evm_empty" empty⟩,
   ⟨144, .globalSaved "evm_empty" empty⟩, ⟨216, .literal 0#64⟩]

def countAssign : ProgHOL 64 := .call (some (some (.local, ofString "acc_n"), none))
  (ofString "htab_count") [messageLoad 160]
def finalProgram : ProgHOL 64 := FieldStores.program "e" "msg" (finalFields 0#64 0#64) (.return (localVar "e"))
def countContinuation : ProgHOL 64 := FieldStores.program "e" "msg" (firstCountFields 0#64)
  (.seq countAssign finalProgram)
def countProgram : ProgHOL 64 := .decCall (ofString "acc_n") .one (ofString "htab_count")
  [messageLoad 152] countContinuation

def deleteContinuation : ProgHOL 64 := FieldStores.program "e" "msg" (deleteFields 0#64 0#64 0#64) countProgram
def logContinuation : ProgHOL 64 := FieldStores.program "e" "msg" (logFields 0#64 0#64)
  (.decCall (ofString "del") .one (ofString "htab_new_scratch") [.const 20#64, .const 4#64] deleteContinuation)
def jumpContinuation : ProgHOL 64 := FieldStores.program "e" "msg" (jumpFields 0#64)
  (.decCall (ofString "logs") .one (ofString "lst_new_scratch") [.const 8#64, .const 4#64] logContinuation)
def suffixProgram : ProgHOL 64 := .decCall (ofString "jd") .one (ofString "compute_jumpdests")
  [messageLoad 112, messageLoad 120] jumpContinuation

set_option maxRecDepth 20000 in
/-- Every remaining instruction of the original constructor, including its
actual assigned second count call and global evm_empty reads. -/
theorem actual_suffix : afterGas = suffixProgram := by
  simp only [afterGas, gasSite, afterZero, body, Guest.guestFn_frame_new, progToHOL,
    expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    suffixProgram, jumpContinuation, logContinuation, deleteContinuation,
    countProgram, countContinuation, countAssign, finalProgram, jumpFields, logFields,
    deleteFields, firstCountFields, finalFields, messageLoad, FieldStores.program,
    FieldStores.address, FieldStores.Value.expression, localVar, addConst]

/-- Exact scalar stores performed by the count suffix. -/
def countWrites (frame addressCount keyCount empty : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  FieldStores.writes frame (firstCountFields addressCount) ++ FieldStores.writes frame (finalFields keyCount empty)

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.actual_suffix
