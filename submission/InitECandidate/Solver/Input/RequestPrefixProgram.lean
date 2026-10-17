import InitECandidate.Solver.Input.RequestProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefixAppend

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def actions : List Action :=
  [.declare "o_npr" (.load .one Header.offsets),
   .declare "o_wit" (.load .one (Scalar.plus Header.offsets 8)),
   .allocate "si" (.const 96#64),.command chainStore,
   .declare "np" pointerExpression,.declare "nlen" lengthExpression]

def loaded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (witness : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind source "o_npr" 16#64) "o_wit" (BitVec.ofNat 64 witness)
def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (witness : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (WitnessRadix.PersistentAlloc.post {loaded source witness with clock:=source.clock-1} cursor 96#64) "si" cursor
def chained (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (cursor : BitVec 64) (witness : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {allocated source cursor witness with memory:=(WitnessRadix.StoreWord.put (allocated source cursor witness).memory
    (cursor+88#64) (BitVec.ofNat 64 (Guest.GasLimit.le64 input 10)))}
def positioned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64) (witness : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (chained source input cursor witness) "np" (pointer+18#64)
def prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64) (witness : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  WitnessRadix.QueryBranch.bind (positioned source input pointer cursor witness) "nlen" (BitVec.ofNat 64 (witness-16))

def restorePrefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor : BitVec 64) (witness : Nat) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  restore source "o_npr" (restore (WitnessRadix.QueryBranch.bind source "o_npr" 16#64) "o_wit"
    (restore (loaded source witness) "si" (restore (chained source input cursor witness) "np"
      (restore (positioned source input pointer cursor witness) "nlen" target))))

theorem actions_shape : prefixBody=program actions (.seq lengthGuard requestBody) := by
  rw [prefix_shape]
  rfl

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.actions_shape
