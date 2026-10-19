import InitECandidate.Solver.Rlp.ItemTotalCall

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_list_count with | .function fn=>progToHOL fn.body | _=>.skip
def loop : ProgHOL 64 := match body with | .dec _ _ _ (.dec _ _ _ (.seq first _))=>first | _=>.skip
def condition : ExpHOL 64 := .cmp .lower (localVar "off") (localVar "len")
def advance : ProgHOL 64 := .seq (.assign .local (ofString "off") (.op .add [localVar "off",localVar "total"]))
  (.assign .local (ofString "count") (.op .add [localVar "count",.const 1#64]))
def arguments : List (ExpHOL 64) := [.op .add [localVar "p",localVar "off"],.op .sub [localVar "len",localVar "off"]]
def loopBody : ProgHOL 64 := .decCall (ofString "total") .one (ofString "rlp_item_total") arguments advance

theorem body_shape : body=.dec (ofString "count") .one (.const 0#64)
    (.dec (ofString "off") .one (.const 0#64) (.seq loop (.return (localVar "count")))) := by
  simp only [body,loop,localVar,Guest.guestFn_rlp_list_count,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
theorem loop_shape : loop=.while condition loopBody := by
  simp only [loop,body,condition,loopBody,arguments,advance,localVar,Guest.guestFn_rlp_list_count,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_list_count")=some (Header.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 101 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_list_count) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,
    Guest.guestFn_rlp_list_count,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64) : Prop where
  arena : Validation.Arena source cursor limit
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))
  countCell : source.locals.lookup (ofString "count")=some (.val (.word count))
  counted : count.toNat≤offset.toNat
  bounded : offset.toNat≤length.toNat
  fits : pointer.toNat+length.toNat<2^64

theorem View.clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) (clock : Nat) :
    View {source with clock:=clock} pointer length cursor limit offset count :=
  ⟨Validation.Arena.of_fields source _ cursor limit view.arena rfl rfl,view.pointerCell,view.lengthCell,view.offsetCell,view.countCell,view.counted,view.bounded,view.fits⟩

def Invariant (pointer length cursor limit : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ offset count,View source pointer length cursor limit offset count
def allowance (length : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  60*(length.toNat-(Validation.localWord source "off").toNat)+31

theorem allowance_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length offset : BitVec 64)
    (cell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    allowance length source=60*(length.toNat-offset.toNat)+31 := by simp only [allowance,Validation.localWord,cell]

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.body_shape
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_shape
#print axioms InitECandidate.Solver.Rlp.ListCount.original_code
#print axioms InitECandidate.Solver.Rlp.ListCount.View.clock
#print axioms InitECandidate.Solver.Rlp.ListCount.allowance_eq
