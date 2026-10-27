import InitECandidate.Solver.Input.DropLeading
import InitECandidate.Solver.Input.PayloadProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefixAppend

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def offsetBody : ProgHOL 64 := dropLeading 7 afterGuard
def pointerStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 0) (localVar "p")
def lengthStore : ProgHOL 64 := .store (Scalar.plus (localVar "pl") 8) (localVar "len")
def prefixActions : List Action := [
  .allocate "pl" (.const 136#64),.command pointerStore,.command lengthStore,
  .declare "o_extra" (Scalar.flat32 (localVar "p") [436]),
  .declare "o_txs" (Scalar.flat32 (localVar "p") [504]),
  .declare "o_wd" (Scalar.flat32 (localVar "p") [508]),
  .declare "o_bal" (Scalar.flat32 (localVar "p") [528])]

/-- Exact allocated payload header and all four offset declarations, before
its real count-four/fixed-540 validator. -/
theorem prefix_shape : afterGuard=program prefixActions offsetBody := by
  simp only [afterGuard,body,Scalar.payloadBody,Guest.Software.guestFn_decode_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,offsetBody,dropLeading,prefixActions,program,pointerStore,lengthStore,
    Scalar.plus,Scalar.flat32,Scalar.flatAddress,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  bind (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" cursor
def pointerStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor : BitVec 64) :=
  {allocated source cursor with memory:=WitnessRadix.StoreWord.put source.memory cursor (pointer+62#64)}
def headerStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor length : BitVec 64) :=
  {pointerStored source pointer cursor with memory:=WitnessRadix.StoreWord.put (pointerStored source pointer cursor).memory (cursor+8#64) length}
def offsetWords (input : Guest.InputBlob) (position : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (Guest.GasLimit.le32 input (if position=0 then 498 else if position=1 then 566 else if position=2 then 570 else 590))

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.prefix_shape
