import InitECandidate.Solver.MutableTable.ItemScopedNormal
import InitECandidate.Solver.MutableTable.GetCall32
import InitECandidate.Solver.GasBudget.JournalZoneSetValues
import InitECandidate.Solver.MutableTable.WitnessBuildBudget

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_destroy_storage with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "addr",.one)]
def transactionTable (offset : BitVec 64) : ExpHOL 64 := .load .one (.op .add [.var .global (ofString "ts"),.const offset])
def condition : ExpHOL 64 := .cmp .less (localVar "i") (localVar "cap")
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def markCall : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set") [transactionTable 24#64,localVar "k",.const 1#64]
def mark : ProgHOL 64 := .decCall (ofString "k") .one (ofString "sk_make") [localVar "addr",.rfield 1 (localVar "s")] markCall
def afterItem : ProgHOL 64 := .seq (.ite (.cmp .notEqual (.rfield 0 (localVar "s")) (.const 0#64)) mark .skip) increment
def loopBody : ProgHOL 64 := .decCall (ofString "s") Slot.tripleShape (ofString "htab_item") [localVar "inner",localVar "i"] afterItem
def loop : ProgHOL 64 := .while condition loopBody
def removeCall : ProgHOL 64 := .call (some (none,none)) (ofString "jdel") [localVar "outer",localVar "addr"]
def present : ProgHOL 64 := .dec (ofString "inner") .one (.rfield 1 (localVar "m"))
  (.dec (ofString "cap") .one (.load .one (.op .add [localVar "inner",.const 24#64]))
    (.dec (ofString "i") .one (.const 0#64) (.seq loop (.seq removeCall (.return (.const 0#64))))))
def afterGet : ProgHOL 64 := .seq (.ite (.cmp .equal (.rfield 0 (localVar "m")) (.const 0#64)) (.return (.const 0#64)) .skip) present

theorem body_shape : body = .dec (ofString "outer") .one (transactionTable 32#64)
    (.decCall (ofString "m") Get.pairShape (ofString "htab_get") [localVar "outer",localVar "addr"] afterGet) := by
  simp only [body,transactionTable,afterGet,present,loop,condition,loopBody,afterItem,mark,markCall,increment,removeCall,localVar,
    Slot.tripleShape,Get.pairShape,Guest.guestFn_destroy_storage,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "destroy_storage") = some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 357 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_destroy_storage) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Guest.guestFn_destroy_storage,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def loopPrice (population remaining : Nat) : Nat := (13 * population + 32) * remaining + 13 * WitnessBuild.triangle remaining

theorem loop_price_step (population remaining : Nat) :
    loopPrice population (remaining + 1) = 13 * population + 32 + loopPrice (population + 1) remaining := by
  simp only [loopPrice,WitnessBuild.triangle,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
  omega

theorem mark_price (population : Nat) : Set.noGrowthPrice .storage population + 1 = 13 * population + 16 := by
  simp [Set.noGrowthPrice,Insert.findPrice,Insert.rawPrice,Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price]
  omega

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.body_shape
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.original_code
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.loop_price_step
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.mark_price
