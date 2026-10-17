import InitECandidate.Solver.Input.HostLength
import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_input_blob with
  | .function fn => progToHOL fn.body | _ => .skip

def loadLength : ProgHOL 64 := .shMemLoad .opW .local (ofString "len") (.const 1073741832#64)
def oversized : ExpHOL 64 := .cmp .lower (.const 134217712#64) (localVar "len")
def guard : ProgHOL 64 := .ite oversized (.call (some (none,none)) (ofString "trap_with") [.const 8#64]) .skip

def afterGuard : ProgHOL 64 := match body with
  | .dec _ _ _ (.seq _ (.seq _ rest)) => rest
  | _ => .skip

def copyCondition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "len")
def dataAddress : ExpHOL 64 := .op .add [.const 1073741840#64,localVar "i"]
def copyBody : ProgHOL 64 := .seq (.shMemLoad .opW .local (ofString "w") dataAddress)
  (.seq (.store (.op .add [localVar "p",localVar "i"]) (localVar "w"))
    (.assign .local (ofString "i") (addConst (localVar "i") 8#64)))
def copyLoop : ProgHOL 64 := .while copyCondition copyBody

theorem body_shape : body=.dec (ofString "len") .one (.const 0#64)
    (.seq loadLength (.seq guard afterGuard)) := by
  simp only [body,Guest.guestFn_input_blob,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    loadLength,guard,oversized,localVar,afterGuard,Option.map_none]

theorem after_guard_shape : afterGuard=.decCall (ofString "p") .one (ofString "alloc")
    [addConst (localVar "len") 8#64]
    (.dec (ofString "i") .one (.const 0#64) (.dec (ofString "w") .one (.const 0#64)
      (.seq copyLoop (.return (.rstruct [localVar "p",localVar "len"]))))) := by
  simp only [afterGuard,body,Guest.guestFn_input_blob,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    copyLoop,copyCondition,copyBody,dataAddress,localVar,addConst,Option.map_none]

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.body_shape
#print axioms InitECandidate.Solver.Input.Blob.after_guard_shape
