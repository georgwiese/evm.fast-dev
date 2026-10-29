import InitECandidate.Solver.Input.RlpLength.BeCall
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.Input.RlpWrite.PutBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_put_be with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "v",.one),(ofString "n",.one)]
def test : ExpHOL 64 := .cmp .lower (.const 0#64) (localVar "i")
def decrement : ExpHOL 64 := .op .sub [localVar "i",.const 1#64]
def address : ExpHOL 64 := .op .add [localVar "dst",localVar "i"]
def shifted : ExpHOL 64 := .shift .lsr (localVar "v") (.const 8#64)
def loopBody : ProgHOL 64 := .seq (.assign .local (ofString "i") decrement)
  (.seq (.storeByte address (localVar "v")) (.assign .local (ofString "v") shifted))
def loop : ProgHOL 64 := .while test loopBody
def tail : ProgHOL 64 := .seq loop (.return (.const 0#64))

theorem body_shape : body=.dec (ofString "i") .one (localVar "n") tail := by
  simp only [body,Guest.guestFn_rlp_put_be,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    tail,loop,test,loopBody,decrement,address,shifted,localVar]

def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (index : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind {bind source "i" (BitVec.ofNat 64 index) with
    memory:=WitnessRadix.ByteStore.put source.memory source.be (dst+BitVec.ofNat 64 index) (BitVec.ofNat 8 value.toNat)} "v" (value >>> (8:Nat))

theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst value : BitVec 64) (index : Nat) (small : index+1<2^64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))))
    (v : source.locals.lookup (ofString "v")=some (.val (.word value)))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) :
    evaluateHOLFiniteState source loopBody=(none,step source dst value index) := by
  classical
  have subtraction : BitVec.ofNat 64 (index+1)-1#64=BitVec.ofNat 64 index := by
    rw [show (1#64 : BitVec 64)=BitVec.ofNat 64 1 from rfl,BitVec.ofNat_sub_ofNat_of_le (w:=64) (index+1) 1 (by decide) (by omega)]
    congr 1
  have decRead : eval source decrement=some (.val (.word (BitVec.ofNat 64 index))) := by
    simp [eval,decrement,localVar,evalHOLExact,evalListHOLExact,toExact,i,valueIsWord,valueWord,wordOpHOL,wordOp,subtraction]
  let si:=bind source "i" (BitVec.ofNat 64 index)
  have decRun:=WitnessRadix.StateSteps.assign_execute source "i" decrement _ _ i decRead
  have iNew : si.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=bind_lookup_same _ _ _
  have dNew : si.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (bind_lookup_other _ "i" "dst" _ (by decide)).trans d
  have vNew : si.locals.lookup (ofString "v")=some (.val (.word value)):=
    (bind_lookup_other _ "i" "v" _ (by decide)).trans v
  have addressRead : eval si address=some (.val (.word (dst+BitVec.ofNat 64 index))) := by
    simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,dNew,iNew,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval si (localVar "v")=some (.val (.word value)) := by simp [eval,localVar,evalHOLExact,toExact,vNew]
  have storeRun:=WitnessRadix.ByteStore.execute_word si address (localVar "v") (dst+BitVec.ofNat 64 index) value addressRead valueRead mapped
  let written:={si with memory:=WitnessRadix.ByteStore.put si.memory si.be (dst+BitVec.ofNat 64 index) (BitVec.ofNat 8 value.toNat)}
  have vWritten : written.locals.lookup (ofString "v")=some (.val (.word value)):=vNew
  have shiftRead : eval written shifted=some (.val (.word (value >>> (8:Nat)))) := by
    simp [eval,shifted,localVar,evalHOLExact,toExact,vWritten,wordShiftHOL]
  have shiftRun:=WitnessRadix.StateSteps.assign_execute written "v" shifted _ _ vNew shiftRead
  rw [loopBody,WitnessRadix.StateSteps.next_sequence source si _ _ decRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence si written _ _ storeRun (Nat.le_refl _)]
  exact shiftRun

end InitECandidate.Solver.Input.RlpWrite.PutBe

#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.PutBe.step_execute
