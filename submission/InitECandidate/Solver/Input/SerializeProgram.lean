import InitECandidate.Solver.Input.LittleEndianWriters
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.CopyGeneralCall

namespace InitECandidate.Solver.Input.Serialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_serialize_result with | .function fn => progToHOL fn.body | _ => .skip
def address (offset : Nat) : ExpHOL 64 := .op .add [localVar "out",.const (BitVec.ofNat 64 offset)]
def copyArgs : List (ExpHOL 64) := [localVar "out",localVar "root",.const 32#64]
def chainArgs : List (ExpHOL 64) := [address 33,localVar "chain_id"]
def successStore : ProgHOL 64 := .storeByte (address 32) (localVar "succ")
def schemaLow : ExpHOL 64 := .op .and [localVar "schema_id",.const 255#64]
def schemaHigh : ExpHOL 64 := .shift .lsr (localVar "schema_id") (.const 8#64)
def tail : ProgHOL 64 := .seq (.storeByte (address 41) schemaLow) (.seq (.storeByte (address 42) schemaHigh) (.return (.const 43#64)))
def formals : List (MlS × ShapeHOL) := [(ofString "out",.one),(ofString "root",.one),(ofString "succ",.one),(ofString "chain_id",.one),(ofString "schema_id",.one)]
def copied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root : BitVec 64) := CopyGeneral.callState source root out 32
def succeeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out succ : BitVec 64) :=
  {source with memory := ByteStore.put source.memory source.be (out + 32#64) (BitVec.ofNat 8 succ.toNat)}
def chained (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out chain : BitVec 64) :=
  {source with memory := MemoryWordCalls.le64Image source.memory source.be (out + 33#64) chain,clock := source.clock - 3}
def schemaState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out schema : BitVec 64) :=
  {source with memory := ByteStore.put (ByteStore.put source.memory source.be (out + 41#64) (BitVec.ofNat 8 (schema &&& 255#64).toNat)) source.be (out + 42#64) (BitVec.ofNat 8 (schema >>> 8).toNat)}
def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root succ chain schema : BitVec 64) :=
  schemaState (chained (succeeded (copied source out root) out succ) out chain) out schema

theorem original_shape : body = .seq (.call (some (none,none)) (ofString "memcpy") copyArgs)
    (.seq successStore (.seq (.call (some (none,none)) (ofString "st_le64") chainArgs) tail)) := by
  simp only [body,Guest.guestFn_serialize_result,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,
    copyArgs,successStore,chainArgs,tail,address,schemaLow,schemaHigh,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "serialize_result") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 204 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_serialize_result) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_serialize_result,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Serialize

#print axioms InitECandidate.Solver.Input.Serialize.original_shape
#print axioms InitECandidate.Solver.Input.Serialize.original_code
