import InitECandidate.Solver.Rlp.CurrentItem.Call
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual transaction-specific consumers of the existing current RLP item
parser. Each reads one real slice-array row and checks its own field shape. -/
inductive Kind where
  | scalar | bytes | fixed | destination | list

def declaration : Kind → Decl (BitVec 64)
  | .scalar => Guest.Software.guestFn_tx_scalar_item
  | .bytes => Guest.Software.guestFn_tx_bytes_item
  | .fixed => Guest.Software.guestFn_tx_fixed_bytes
  | .destination => Guest.Software.guestFn_tx_to_item
  | .list => Guest.Software.guestFn_tx_list_item

def name : Kind → String
  | .scalar => "tx_scalar_item"
  | .bytes => "tx_bytes_item"
  | .fixed => "tx_fixed_bytes"
  | .destination => "tx_to_item"
  | .list => "tx_list_item"

def formals : Kind → List (MlS×ShapeHOL)
  | .scalar => [(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)]
  | .bytes => [(ofString "arr",.one),(ofString "i",.one)]
  | .fixed => [(ofString "arr",.one),(ofString "i",.one),(ofString "width",.one)]
  | .destination => [(ofString "arr",.one),(ofString "i",.one)]
  | .list => [(ofString "arr",.one),(ofString "i",.one)]

def resultShape : Kind → ShapeHOL
  | .scalar => .comb [.one,.one]
  | .bytes => .comb [.one,.one]
  | .fixed => .one
  | .destination => .one
  | .list => .comb [.one,.one]

def body (kind : Kind) : ProgHOL 64:=match declaration kind with | .function fn=>progToHOL fn.body | _=>.skip
def tail (kind : Kind) : ProgHOL 64:=match body kind with | .decCall _ _ _ _ rest=>rest | _=>.skip

def rowArguments : List (ExpHOL 64):=[
  .load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]),
  .load .one (.op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64])]

set_option maxRecDepth 100000 in
theorem body_shape (kind : Kind) :
    body kind=.decCall (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") rowArguments (tail kind) := by
  cases kind <;> simp only [body,tail,declaration,rowArguments,Rlp.Item.resultShape,
    Guest.Software.guestFn_tx_scalar_item,Guest.Software.guestFn_tx_bytes_item,Guest.Software.guestFn_tx_fixed_bytes,Guest.Software.guestFn_tx_to_item,Guest.Software.guestFn_tx_list_item,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

set_option maxRecDepth 100000 in
/-- The actual field guards and final return do no calls or writes. Their
reads may fail or reject without adding source call/loop ticks. -/
theorem tail_pure (kind : Kind) : PureDecision (tail kind) := by
  cases kind <;> simp only [tail,body,declaration,
    Guest.Software.guestFn_tx_scalar_item,Guest.Software.guestFn_tx_bytes_item,Guest.Software.guestFn_tx_fixed_bytes,Guest.Software.guestFn_tx_to_item,Guest.Software.guestFn_tx_list_item,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  all_goals
    repeat' first
      | apply PureDecision.seq
      | apply PureDecision.ite
      | exact PureDecision.raised _ _
      | exact PureDecision.returned _
      | exact PureDecision.skip

/-- Read-only decisions retain all nonlocals on every outcome. -/
theorem decision_readonly {program : ProgHOL 64} (decision : PureDecision program) (code) :
    LocalEffects.Preserves code program := by
  induction decision with
  | skip=>exact LocalEffects.skip code
  | returned expression=>exact LocalEffects.returned code expression
  | raised tag expression=>exact LocalEffects.raised code tag expression
  | ite test left right first second=>exact LocalEffects.conditional code test _ _ first second
  | seq front back first second=>exact LocalEffects.sequence code _ _ first second

/-- Real row bindings, mapped cells and their actual contents determine
both arguments. No later parser return or successful future read is assumed. -/
theorem row_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array index pointer length : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (pointerMapped : source.memaddrs (array+index*16#64))
    (lengthMapped : source.memaddrs (array+index*16#64+8#64))
    (pointerStored : source.memory (array+index*16#64)=.word pointer)
    (lengthStored : source.memory (array+index*16#64+8#64)=.word length) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length) := by
  simp only [BitVec.add_assoc] at lengthMapped lengthStored
  simp [rowArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,arrayCell,indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,BitVec.add_assoc,pointerMapped,lengthMapped,pointerStored,lengthStored]

/-- Complete actual reader body cost, including parsing, all shape/length
rejections, scratch exhaustion and other stopped outcomes. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer length : BitVec 64)
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (body kind)).2.clock≤60*length.toNat+11 := by
  rw [body_shape]
  have price:=Rlp.CurrentItem.scoped_valid_cost source pointer length arena fits "it" rowArguments (tail kind) 0 args (by
    intro current answer valid frame
    let resumed:=setVarHOLFinite (ofString "it") answer {current with locals:=source.locals}
    exact ClockCost.of_quiet resumed.code (tail kind) ((tail_pure kind).quiet resumed.code) resumed rfl)
  simpa only [Nat.add_zero] using price

/-- A genuine normal field return retains the actual restored scratch
cursors and every memory word outside temporary RLP scratch. -/
theorem body_normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer length : BitVec 64)
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    Rlp.CurrentItem.Frame source target := by
  rw [body_shape] at normal
  obtain ⟨item,child,inner,valid,forward,price,frame,continued,endpoint⟩:=
    Rlp.CurrentItem.scoped_normal source target pointer length arena fits "it" rowArguments (tail kind) args value normal
  have readonly:=decision_readonly (tail_pure kind) child.code
    (setVarHOLFinite (ofString "it") item {child with locals:=source.locals}) rfl
  rw [continued] at readonly
  have final : LocalEffects.erase target=LocalEffects.erase child:=by
    rw [endpoint]
    exact readonly
  exact frame.of_erase rfl final

/-- A final return preceded only by real rejecting guards. -/
inductive GuardedReturn (expression : ExpHOL 64) : ProgHOL 64→Prop where
  | returned : GuardedReturn expression (.return expression)
  | guard {front back : ProgHOL 64} (first : PureGuard front) (last : GuardedReturn expression back) :
      GuardedReturn expression (.seq front back)

theorem GuardedReturn.normal {expression : ExpHOL 64} {program : ProgHOL 64}
    (shape : GuardedReturn expression program) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source program=(some (.returned value),target)) :
    eval source expression=some value ∧ target=emptyLocalsHOLFinite source := by
  induction shape with
  | returned=>exact return_normal source target expression value actual
  | guard first last ih=>exact ih (first.normal_continue source target _ value actual)

def pairExpression : ExpHOL 64:=.rstruct [.rfield 1 (localVar "it"),.rfield 2 (localVar "it")]

set_option maxRecDepth 100000 in
/-- Scalar, bytes and list helpers return the genuine decoded payload pair. -/
theorem pair_tail (kind : Kind) (paired : kind=.scalar ∨ kind=.bytes ∨ kind=.list) :
    GuardedReturn pairExpression (tail kind) := by
  rcases paired with rfl|rfl|rfl
  all_goals
    simp only [tail,body,declaration,pairExpression,localVar,
      Guest.Software.guestFn_tx_scalar_item,Guest.Software.guestFn_tx_bytes_item,Guest.Software.guestFn_tx_list_item,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
    repeat' first
      | apply GuardedReturn.guard
      | exact GuardedReturn.returned
      | apply PureGuard.seq
      | apply PureGuard.ite
      | exact PureGuard.raise _ _
      | exact PureGuard.skip

/-- The normal returned pair comes from the actual positive contained RLP
item. This supplies its physical payload extent to the transaction decoder. -/
theorem body_pair_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer length : BitVec 64)
    (paired : kind=.scalar ∨ kind=.bytes ∨ kind=.list)
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    ∃ header payload flag,Rlp.Item.Valid pointer length.toNat (Rlp.Item.result pointer header payload flag) ∧
      value=.rStruct [.val (.word (pointer+header)),.val (.word payload)] ∧ Rlp.CurrentItem.Frame source target := by
  have total:=body_normal_frame source target kind pointer length arena fits args value normal
  rw [body_shape] at normal
  obtain ⟨item,child,inner,valid,forward,price,frame,continued,endpoint⟩:=
    Rlp.CurrentItem.scoped_normal source target pointer length arena fits "it" rowArguments (tail kind) args value normal
  obtain ⟨header,payload,flag,same,rest⟩:=valid
  let resumed:=setVarHOLFinite (ofString "it") item {child with locals:=source.locals}
  have actual : evaluateHOLFiniteState resumed (tail kind)=(some (.returned value),inner):=continued
  obtain ⟨read,finished⟩:=(pair_tail kind paired).normal resumed inner value actual
  have expected : eval resumed pairExpression=some (.rStruct [.val (.word (pointer+header)),.val (.word payload)]):=by
    simp [resumed,pairExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,same,Rlp.Item.result]
  exact ⟨header,payload,flag,⟨header,payload,flag,rfl,rest⟩,Option.some.inj (read.symm.trans expected),total⟩

def rejectUnequal (left right : ExpHOL 64) (code : BitVec 64) : ProgHOL 64:=
  .ite (.cmp .notEqual left right) (.raise (ofString "TxErr") (.const code)) .skip

/-- Even a missing exception shape cannot make a failed equality check
continue. The equality comes from the actual reached guard. -/
theorem reject_unequal_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (left right : ExpHOL 64) (code first second : BitVec 64)
    (firstRead : eval source left=some (.val (.word first)))
    (secondRead : eval source right=some (.val (.word second)))
    (normal : evaluateHOLFiniteState source (rejectUnequal left right code)=(none,target)) : first=second := by
  by_contra different
  have observed : eval source (.cmp .notEqual left right)=some (.val (.word 1#64)):=by
    simp only [eval] at firstRead secondRead ⊢
    simp [evalHOLExact,firstRead,secondRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different]
  have selected : evaluateHOLFiniteState source (rejectUnequal left right code)=
      evaluateHOLFiniteState source (.raise (ofString "TxErr") (.const code)):=by
    rw [rejectUnequal,evaluateHOLFiniteState_ite]
    simp only [eval] at observed
    rw [observed]
    rfl
  rw [selected] at normal
  exact raise_ne_none source (ofString "TxErr") (.const code) (congrArg Prod.fst normal)

set_option maxRecDepth 100000 in
theorem fixed_tail_shape : tail .fixed=
    .seq (rejectUnequal (.rfield 0 (localVar "it")) (.const 0#64) 15#64)
      (.seq (rejectUnequal (.rfield 2 (localVar "it")) (localVar "width") 16#64)
        (.return (.rfield 1 (localVar "it")))) := by
  simp only [tail,body,declaration,rejectUnequal,localVar,Guest.Software.guestFn_tx_fixed_bytes,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

/-- The fixed-width helper's actual normal return proves the decoded
payload has exactly that width and is bytes, inside its original item span. -/
theorem body_fixed_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length width : BitVec 64)
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (widthCell : source.locals.lookup (ofString "width")=some (.val (.word width)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body .fixed)=(some (.returned value),target)) :
    ∃ header,Rlp.Item.Valid pointer length.toNat (Rlp.Item.result pointer header width 0#64) ∧
      value=.val (.word (pointer+header)) ∧ Rlp.CurrentItem.Frame source target := by
  have total:=body_normal_frame source target .fixed pointer length arena fits args value normal
  rw [body_shape] at normal
  obtain ⟨item,child,inner,valid,forward,price,frame,continued,endpoint⟩:=
    Rlp.CurrentItem.scoped_normal source target pointer length arena fits "it" rowArguments (tail .fixed) args value normal
  obtain ⟨header,payload,flag,same,rest⟩:=valid
  let resumed:=setVarHOLFinite (ofString "it") item {child with locals:=source.locals}
  have actual : evaluateHOLFiniteState resumed (tail .fixed)=(some (.returned value),inner):=continued
  have fieldRead (offset : Nat) : eval resumed (.rfield offset (localVar "it"))=
      eval resumed (.rfield offset (.rstruct [.const flag,.const (pointer+header),.const payload,.const (header+payload)])):=by
    simp [resumed,eval,evalHOLExact,evalListHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,same,Rlp.Item.result]
  have flagRead : eval resumed (.rfield 0 (localVar "it"))=some (.val (.word flag)):=by rw [fieldRead]; rfl
  have lengthRead : eval resumed (.rfield 2 (localVar "it"))=some (.val (.word payload)):=by rw [fieldRead]; rfl
  have pointerRead : eval resumed (.rfield 1 (localVar "it"))=some (.val (.word (pointer+header))):=by rw [fieldRead]; rfl
  have widthRead : eval resumed (localVar "width")=some (.val (.word width)):=by
    simp [resumed,eval,evalHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,widthCell,
      show ofString "it"≠ofString "width" from by decide]
  rw [fixed_tail_shape] at actual
  have first : PureGuard (rejectUnequal (.rfield 0 (localVar "it")) (.const 0#64) 15#64):=.ite _ (.raise _ _) .skip
  have firstRun:=first.normal_passed resumed inner _ value actual
  have zero:=reject_unequal_normal resumed resumed _ _ 15#64 flag 0#64 flagRead rfl firstRun
  have suffix:=first.normal_continue resumed inner _ value actual
  have second : PureGuard (rejectUnequal (.rfield 2 (localVar "it")) (localVar "width") 16#64):=.ite _ (.raise _ _) .skip
  have secondRun:=second.normal_passed resumed inner _ value suffix
  have exactWidth:=reject_unequal_normal resumed resumed _ _ 16#64 payload width lengthRead widthRead secondRun
  have returned:=second.normal_continue resumed inner _ value suffix
  obtain ⟨answer,finished⟩:=return_normal resumed inner (.rfield 1 (localVar "it")) value returned
  subst payload
  subst flag
  exact ⟨header,⟨header,width,0#64,rfl,rest⟩,Option.some.inj (answer.symm.trans pointerRead),total⟩

set_option maxRecDepth 100000 in
theorem original_code (kind : Kind) (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString (name kind))=some (formals kind,body kind,resultShape kind) := by
  cases kind with
  | scalar=>
    have checked:=OriginalCode.indexed code installed 269 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_scalar_item) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,name,formals,body,declaration,resultShape,
      Guest.Software.guestFn_tx_scalar_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | bytes=>
    have checked:=OriginalCode.indexed code installed 272 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_bytes_item) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,name,formals,body,declaration,resultShape,
      Guest.Software.guestFn_tx_bytes_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | fixed=>
    have checked:=OriginalCode.indexed code installed 273 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_fixed_bytes) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,name,formals,body,declaration,resultShape,
      Guest.Software.guestFn_tx_fixed_bytes,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | destination=>
    have checked:=OriginalCode.indexed code installed 274 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_to_item) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,name,formals,body,declaration,resultShape,
      Guest.Software.guestFn_tx_to_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | list=>
    have checked:=OriginalCode.indexed code installed 275 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_list_item) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,name,formals,body,declaration,resultShape,
      Guest.Software.guestFn_tx_list_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentVerify.TransactionFields

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.tail_pure
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.decision_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.row_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.body_normal_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.GuardedReturn.normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.pair_tail

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.body_pair_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.reject_unequal_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.fixed_tail_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionFields.body_fixed_normal
