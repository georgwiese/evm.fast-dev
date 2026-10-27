import InitECandidate.Solver.Input.RequestRequestsProgram
import InitECandidate.Solver.Input.BytesList.Values
import InitECandidate.Solver.Input.VarList.Environment

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 10000

def nodeCall : ProgHOL 64:=Payload.dropLeading 39 Header.body
def afterNode : ProgHOL 64:=Payload.dropLeading 1 nodeCall
def codeCall : ProgHOL 64:=Payload.dropLeading 2 afterNode
def afterCode : ProgHOL 64:=Payload.dropLeading 1 codeCall
def headerCall : ProgHOL 64:=Payload.dropLeading 2 afterCode
def afterHeaders : ProgHOL 64:=Payload.dropLeading 1 headerCall
def returnInput : ProgHOL 64:=.return (localVar "si")
def listArguments (first last : String) (limit maximum : Nat) : List (ExpHOL 64):=[
  .op .add [localVar "wp",localVar first],.op .sub [localVar last,localVar first],
  .const (BitVec.ofNat 64 limit),.const (BitVec.ofNat 64 maximum)]
def pointerStore (name : String) (offset : Nat) : ProgHOL 64:=
  .store (Scalar.plus (localVar "si") offset) (.rfield 0 (localVar name))
def countStore (name : String) (offset : Nat) : ProgHOL 64:=
  .store (Scalar.plus (localVar "si") (offset+8)) (.rfield 1 (localVar name))

/-- The literal decoder suffix makes three real byte-list calls and stores
all six returned pointer/count fields before returning the input structure. -/
theorem arrays_shape :
    nodeCall=.decCall (ofString "st0") VarList.returnShape (ofString "decode_bytes_list")
      (listArguments "w0" "w1" 9223372036854775807 1024) afterNode ∧
    afterNode=.seq (pointerStore "st0" 40) (.seq (countStore "st0" 40) codeCall) ∧
    codeCall=.decCall (ofString "cd") VarList.returnShape (ofString "decode_bytes_list")
      (listArguments "w1" "w2" 9223372036854775807 65536) afterCode ∧
    afterCode=.seq (pointerStore "cd" 56) (.seq (countStore "cd" 56) headerCall) ∧
    headerCall=.decCall (ofString "hd") VarList.returnShape (ofString "decode_bytes_list")
      (listArguments "w2" "wlen" 256 1024) afterHeaders ∧
    afterHeaders=.seq (pointerStore "hd" 72) (.seq (countStore "hd" 72) returnInput) := by
  simp only [nodeCall,afterNode,codeCall,afterCode,headerCall,afterHeaders,Header.body,
    Guest.Software.guestFn_decode_stateless_input,Payload.dropLeading,progToHOL,expToHOL,shapeToHOL,
    listArguments,pointerStore,countStore,returnInput,Scalar.plus,localVar,VarList.returnShape,
    List.map_cons,List.map_nil,Option.map_none,List.nil_append,List.cons_append,List.append_nil]
  trivial

/-- Concrete mathematical offsets yield the exact real ABI arguments. -/
theorem list_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (start first last limit maximum : Nat) (firstName lastName : String)
    (ordered : first≤last) (firstSmall : first<2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (leftLocal : source.locals.lookup (ofString firstName)=some (.val (.word (BitVec.ofNat 64 first))))
    (rightLocal : source.locals.lookup (ofString lastName)=some (.val (.word (BitVec.ofNat 64 last)))) :
    evalListHOLFinite source (h:=fun q=>Classical.propDecidable (source.memaddrs q)) (listArguments firstName lastName limit maximum)=
      some (BytesList.values (pointer+BitVec.ofNat 64 (start+first)) (BitVec.ofNat 64 (last-first))
        (BitVec.ofNat 64 limit) (BitVec.ofNat 64 maximum)) := by
  have difference : BitVec.ofNat 64 last-BitVec.ofNat 64 first=BitVec.ofNat 64 (last-first):=
    BitVec.ofNat_sub_ofNat_of_le _ _ firstSmall ordered
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,listArguments,BytesList.values,
    localVar,wp,leftLocal,rightLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
    BitVec.add_assoc,BitVec.ofNat_add,difference]

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.arrays_shape
#print axioms InitECandidate.Solver.Input.Witness.list_arguments
