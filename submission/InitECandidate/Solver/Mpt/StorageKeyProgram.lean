import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_sk_make with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one),(ofString "key",.one)]
def buffer : ExpHOL 64 := .var .global (ofString "sk_buf")
def firstCopy : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy") [buffer,localVar "addr",.const 20#64]
def secondCopy : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy") [.op .add [buffer,.const 20#64],localVar "key",.const 32#64]
def price (address key scratch : BitVec 64) : Nat := CopyGeneral.cost address scratch 20 + CopyGeneral.cost key (scratch + 20#64) 32 + 2
def resultState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64) :=
  CopyGeneral.callState (CopyGeneral.callState source address scratch 20) key (scratch + 20#64) 32

theorem body_shape : body = .seq firstCopy (.seq secondCopy (.return buffer)) := by
  simp only [body,firstCopy,secondCopy,buffer,localVar,Guest.guestFn_sk_make,progToHOL,expToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "sk_make") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 328 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sk_make) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_sk_make,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem price_bound (address key scratch : BitVec 64) : price address key scratch ≤ 12 := by
  unfold price CopyGeneral.cost
  split <;> split <;> simp [CopyWords.prefixCost,CopyWords.prefixIndex,CopyBytes.suffixCost]

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.body_shape
#print axioms InitECandidate.Solver.Mpt.StorageKey.original_code
#print axioms InitECandidate.Solver.Mpt.StorageKey.price_bound
