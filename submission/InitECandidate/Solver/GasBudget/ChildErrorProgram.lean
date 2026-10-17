import InitECandidate.Solver.GasBudget.Halt

namespace InitECandidate.Solver.GasBudget.ChildError
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_incorporate_child_on_error with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "child",.one)]
def childLoad (offset : BitVec 64) : ExpHOL 64 := .load .one (.op .add [localVar "child",.const offset])
def sumStore (offset : BitVec 64) : ProgHOL 64 := .store (frameAddress offset) (.op .add [frameLoad offset,childLoad offset])
def offsets : List Nat := [64,72,184]
structure Amounts where
  gas : BitVec 64
  state : BitVec 64
  used : BitVec 64
def Amounts.atOffset (values : Amounts) (offset : Nat) : BitVec 64 :=
  if offset=64 then values.gas else if offset=72 then values.state else values.used
def writes (parent : BitVec 64) (p c : Amounts) : List (BitVec 64×BitVec 64) :=
  [(parent+64#64,p.gas+c.gas),(parent+72#64,p.state+c.state),(parent+184#64,p.used+c.used)]

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64) (p c : Amounts) : Prop where
  ev : source.globals.lookup (ofString "ev")=some (.val (.word parent))
  childLocal : source.locals.lookup (ofString "child")=some (.val (.word child))
  parentMapped : ∀ offset∈offsets,source.memaddrs (parent+BitVec.ofNat 64 offset)
  childMapped : ∀ offset∈offsets,source.memaddrs (child+BitVec.ofNat 64 offset)
  parentCells : ∀ offset∈offsets,source.memory (parent+BitVec.ofNat 64 offset)=.word (p.atOffset offset)
  childCells : ∀ offset∈offsets,source.memory (child+BitVec.ofNat 64 offset)=.word (c.atOffset offset)
  separate : ∀ first∈offsets,∀ second∈offsets,parent+BitVec.ofNat 64 first≠child+BitVec.ofNat 64 second

theorem body_shape : body=.seq (sumStore 64#64) (.seq (sumStore 72#64) (.seq (sumStore 184#64) (.return (.const 0#64)))) := by
  simp only [body,Guest.guestFn_incorporate_child_on_error,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,sumStore,frameAddress,frameLoad,childLoad,localVar]

theorem child_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child offset value : BitVec 64)
    (childLocal : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (mapped : source.memaddrs (child+offset)) (stored : source.memory (child+offset)=.word value) :
    eval source (childLoad offset)=some (.val (.word value)) := by
  simp [eval,childLoad,evalHOLExact,evalListHOLExact,toExact,localVar,childLocal,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem sum_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child offset p c : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word parent)))
    (childLocal : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (parentMapped : source.memaddrs (parent+offset)) (childMapped : source.memaddrs (child+offset))
    (parentCell : source.memory (parent+offset)=.word p) (childCell : source.memory (child+offset)=.word c) :
    evaluateHOLFiniteState source (sumStore offset)=(none,{source with memory:=WitnessRadix.StoreWord.put source.memory (parent+offset) (p+c)}) := by
  have parentRead:=frame_read source parent offset p ev parentMapped parentCell
  have childRead:=child_read source child offset c childLocal childMapped childCell
  have sumRead : eval source (.op .add [frameLoad offset,childLoad offset])=some (.val (.word (p+c))) := by
    simp only [eval] at parentRead childRead ⊢
    simp only [evalHOLExact,evalListHOLExact,parentRead,childRead]
    simp [valueIsWord,valueWord,wordOpHOL,wordOp]
  exact WitnessRadix.StoreWord.execute source (frameAddress offset) _ (parent+offset) (p+c) (address_read source parent offset ev) sumRead parentMapped

theorem stored_away (memory : Memory) (address value query old : BitVec 64) (away : query≠address) (stored : memory query=.word old) :
    WitnessRadix.StoreWord.put memory address value query=.word old := by
  simpa only [WitnessRadix.StoreWord.put,if_neg away] using stored

end InitECandidate.Solver.GasBudget.ChildError

#print axioms InitECandidate.Solver.GasBudget.ChildError.body_shape
#print axioms InitECandidate.Solver.GasBudget.ChildError.child_read
#print axioms InitECandidate.Solver.GasBudget.ChildError.sum_execute
#print axioms InitECandidate.Solver.GasBudget.ChildError.stored_away
