import InitECandidate.Solver.Input.RlpWrite.U256MinCall
import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.Input.HeapScope
import InitECandidate.Solver.Input.RlpWrite.Access

namespace InitECandidate.Solver.Input.RlpWrite.U256Put
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_put_u256 with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "dst",.one),(ofString "v",U256Value.tupleShape)]
def afterEncoded : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (localVar "w"))
def afterMinimum : ProgHOL 64 := .decCall (ofString "w") .one (ofString "rlp_encode_bytes") [localVar "dst",localVar "tmp",localVar "n"] afterEncoded
def afterTemporary : ProgHOL 64 := .decCall (ofString "n") .one (ofString "u256_to_be_min") [localVar "v",localVar "tmp"] afterMinimum
def afterMark : ProgHOL 64 := .decCall (ofString "tmp") .one (ofString "alloc") [.const 32#64] afterTemporary

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,Guest.guestFn_rlp_put_u256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    afterMark,afterTemporary,afterMinimum,afterEncoded,localVar]

structure Codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  markCode : source.code.lookup (ofString "heap_mark")=some ([],HeapScope.markBody,.one)
  allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one)
  minCode : source.code.lookup (ofString "u256_to_be_min")=some (U256Min.formals,U256Min.body,.one)
  minCodes : U256Min.Codes source
  bytesCode : source.code.lookup (ofString "rlp_encode_bytes")=some (BytesWrite.formals,BytesWrite.body,.one)
  bytesCodes : BytesWrite.Codes source
  releaseCode : source.code.lookup (ofString "heap_release")=some (HeapScope.releaseFormals,HeapScope.releaseBody,.one)

theorem restore_global (globals : HolFiniteMapExact MlS (ValueHOL 64)) (key : MlS) (old value : ValueHOL 64)
    (saved : globals.lookup key=some old) : (globals.update (key,value)).update (key,old)=globals := by
  apply HolFiniteMapExact.ext
  funext query
  by_cases same : key=query
  · subst query
    simp [HolFiniteMapExact.update,FUPDATE,saved]
  · simp [HolFiniteMapExact.update,FUPDATE,same]

end InitECandidate.Solver.Input.RlpWrite.U256Put

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.body_shape
#print axioms InitECandidate.Solver.Input.RlpWrite.U256Put.restore_global
