import InitECandidate.Solver.Rlp.CurrentItem.Call
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.CurrentU256.Price
import InitECandidate.Solver.Input.CurrentU256.Memory
import InitECandidate.Solver.Input.ClockCostGuardReached

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

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

inductive Kind where
  | word | wide

def body : Kind→ProgHOL 64
  | .word=>match Guest.Software.guestFn_tx_scalar_word with | .function fn=>progToHOL fn.body | _=>.skip
  | .wide=>match Guest.Software.guestFn_tx_scalar_u256 with | .function fn=>progToHOL fn.body | _=>.skip

def afterField (kind : Kind) : ProgHOL 64:=match body kind with | .decCall _ _ _ _ rest=>rest | _=>.skip

def fieldArguments : List (ExpHOL 64):=[localVar "arr",localVar "i",localVar "maxb"]
def pair (pointer length : BitVec 64) : ValueHOL 64:=.rStruct [.val (.word pointer),.val (.word length)]
def limitTest (cap : BitVec 64) : ExpHOL 64:=.cmp .lower (.const cap) (.rfield 1 (localVar "f"))
def limitGuard (cap : BitVec 64) (error : ExpHOL 64) : ProgHOL 64:=.ite (limitTest cap) (.raise (ofString "TxErr") error) .skip

def wordAfterGuard : ProgHOL 64:=match afterField .word with | .seq _ rest=>rest | _=>.skip
def wordAfterV : ProgHOL 64:=match wordAfterGuard with | .dec _ _ _ rest=>rest | _=>.skip
def wordLoopAndReturn : ProgHOL 64:=match wordAfterV with | .dec _ _ _ rest=>rest | _=>.skip
def wordTest : ExpHOL 64:=.cmp .lower (localVar "j") (.rfield 1 (localVar "f"))
def wordIteration : ProgHOL 64:=match wordLoopAndReturn with | .seq (.while _ iteration) _=>iteration | _=>.skip
def wordAssign : ExpHOL 64:=.op .or [.shift .lsl (localVar "v") (.const 8#64),.loadByte (.op .add [.rfield 0 (localVar "f"),localVar "j"])]
def wideCall : ProgHOL 64:=.call none (ofString "u256_from_be") [.rfield 0 (localVar "f"),.rfield 1 (localVar "f")]

set_option maxRecDepth 100000 in
theorem shapes (kind : Kind) : body kind=.decCall (ofString "f") (.comb [.one,.one]) (ofString "tx_scalar_item") fieldArguments (afterField kind) := by
  cases kind <;> simp only [body,afterField,fieldArguments,localVar,Guest.Software.guestFn_tx_scalar_word,Guest.Software.guestFn_tx_scalar_u256,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

set_option maxRecDepth 100000 in
theorem word_shapes : afterField .word=.seq (limitGuard 8#64 (localVar "envcode")) wordAfterGuard ∧
    wordAfterGuard=.dec (ofString "v") .one (.const 0#64) wordAfterV ∧
    wordAfterV=.dec (ofString "j") .one (.const 0#64) wordLoopAndReturn ∧
    wordLoopAndReturn=.seq (.while wordTest wordIteration) (.return (localVar "v")) ∧
    wordIteration=.seq (.assign .local (ofString "v") wordAssign) (.assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])) := by
  simp only [afterField,body,wordAfterGuard,wordAfterV,wordLoopAndReturn,wordIteration,wordTest,wordAssign,limitGuard,limitTest,localVar,
    Guest.Software.guestFn_tx_scalar_word,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

set_option maxRecDepth 100000 in
theorem wide_shape : afterField .wide=.seq (limitGuard 32#64 (.const 13#64)) wideCall := by
  simp only [afterField,body,limitGuard,limitTest,wideCall,localVar,Guest.Software.guestFn_tx_scalar_u256,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

/-- The actual numeric width rejection supplies its own cap on a real
continuing path, even if exception lookup or the error expression fails. -/
theorem limit_of_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cap : BitVec 64) (error : ExpHOL 64)
    (fCell : source.locals.lookup (ofString "f")=some (pair pointer length))
    (normal : evaluateHOLFiniteState source (limitGuard cap error)=(none,post)) : length.toNat≤cap.toNat := by
  by_contra bad
  have greater : cap.toNat<length.toNat:=by omega
  have observed : eval source (limitTest cap)=some (.val (.word 1#64)):=by
    simp [eval,limitTest,evalHOLExact,toExact,localVar,fCell,pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,greater]
  have selected : evaluateHOLFiniteState source (limitGuard cap error)=evaluateHOLFiniteState source (.raise (ofString "TxErr") error):=by
    rw [limitGuard,evaluateHOLFiniteState_ite]
    simp only [eval] at observed
    rw [observed]
    rfl
  rw [selected] at normal
  exact raise_ne_none source (ofString "TxErr") error (congrArg Prod.fst normal)

theorem word_iteration_cost (code) : ClockCost.Bound code wordIteration 0 := by
  rw [word_shapes.2.2.2.2]
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _)

theorem word_iteration_advance : CounterFlow.Advances (ofString "j") 1 wordIteration := by
  rw [word_shapes.2.2.2.2]
  simpa only [Nat.zero_add,localVar] using CounterFlow.sequence (ofString "j") _ _ 0 1
    (CounterFlow.preserved _ _ (.assign (ofString "v") wordAssign (by decide))) (CounterFlow.increment _)

theorem word_iteration_saved : LocalFlow (ofString "f") wordIteration := by
  rw [word_shapes.2.2.2.2]
  exact .base (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))

/-- Real byte-fold iteration count, independent of byte-read success. -/
theorem word_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fCell : source.locals.lookup (ofString "f")=some (pair pointer length))
    (jCell : source.locals.lookup (ofString "j")=some (.val (.word 0#64))) :
    source.clock-(evaluateHOLFiniteState source (.while wordTest wordIteration)).2.clock≤length.toNat := by
  have price:=CounterFlow.loop_snapshot_cost source.code (ofString "j") (ofString "f") (some (pair pointer length)) wordTest wordIteration 0 length.toNat length.isLt
    (by
      intro current index indexCell fCell bounded
      simp [evalHOLFinite,wordTest,evalHOLExact,toExact,localVar,indexCell,fCell,pair,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def])
    (word_iteration_cost source.code) word_iteration_advance word_iteration_saved source 0#64 rfl jCell fCell (by simp)
  simpa only [Nat.zero_add,Nat.one_mul,BitVec.toNat_zero,Nat.sub_zero] using price

/-- The actual two initializations and loop remain bounded at the width
already observed from the preceding guard. -/
theorem word_after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fCell : source.locals.lookup (ofString "f")=some (pair pointer length)) (small : length.toNat≤8) :
    source.clock-(evaluateHOLFiniteState source wordAfterGuard).2.clock≤8 := by
  rw [word_shapes.2.1]
  apply ClockCost.declared_current source "v" (.const 0#64) 0#64 wordAfterV 8 rfl
  let first:=QueryBranch.bind source "v" 0#64
  have firstF : first.locals.lookup (ofString "f")=some (pair pointer length):=(bind_lookup_other source "v" "f" 0#64 (by decide)).trans fCell
  rw [word_shapes.2.2.1]
  apply ClockCost.declared_current first "j" (.const 0#64) 0#64 wordLoopAndReturn 8 rfl
  let entered:=QueryBranch.bind first "j" 0#64
  have nextF : entered.locals.lookup (ofString "f")=some (pair pointer length):=(bind_lookup_other first "j" "f" 0#64 (by decide)).trans firstF
  have loopPrice:=(word_loop_cost entered pointer length nextF (bind_lookup_same _ _ _)).trans small
  rw [word_shapes.2.2.2.1]
  exact ClockCost.sequence_current entered _ _ 8 0 loopPrice (ClockCost.returned entered.code _)

/-- Cap supplied by this actual guard, not an entry hypothesis. -/
theorem word_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (fCell : source.locals.lookup (ofString "f")=some (pair pointer length)) :
    source.clock-(evaluateHOLFiniteState source (afterField .word)).2.clock≤8 := by
  rw [word_shapes.1]
  have price:=ClockCost.stopping_guard_reached source (limitTest 8#64) (.raise (ofString "TxErr") (localVar "envcode")) wordAfterGuard 0 8
    (raise_ne_none _ _ _) (ClockCost.raised source.code _ _ source rfl) (by
      intro passed
      exact word_after_guard_cost source pointer length fCell (limit_of_normal source source pointer length 8#64 _ fCell passed))
  exact price

/-- The real uint256 tail call has its own existing checked conversion
allowance and can stop on malformed memory without exceeding it. -/
theorem wide_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (fCell : source.locals.lookup (ofString "f")=some (pair pointer length)) :
    source.clock-(evaluateHOLFiniteState source (afterField .wide)).2.clock≤33 := by
  rw [wide_shape]
  have price:=ClockCost.stopping_guard_reached source (limitTest 32#64) (.raise (ofString "TxErr") (.const 13#64)) wideCall 0 33
    (raise_ne_none _ _ _) (ClockCost.raised source.code _ _ source rfl) (by
      intro passed
      have small : length.toNat≤32:=limit_of_normal source source pointer length 32#64 _ fCell passed
      obtain ⟨callee,called,pCell,nCell⟩:=word_pair_environment source.code.lookup (ofString "u256_from_be") (ofString "p") (ofString "n")
        CurrentU256.body RlpWrite.U256Value.tupleShape pointer length (by decide) (CurrentU256.original_code source.code installed)
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.rfield 0 (localVar "f"),.rfield 1 (localVar "f")]=
          some [.val (.word pointer),.val (.word length)]:=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,fCell,pair]
      have currentLength : (callEntryStateHOLFinite source callee).locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length.toNat))):=by
        simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
        exact nCell
      have bodyPrice:=CurrentU256.body_price (callEntryStateHOLFinite source callee) installed length.toNat length.isLt currentLength
      have capped : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentU256.body).2.clock≤32:=bodyPrice.trans (by omega)
      exact ClockCost.call_current source none (ofString "u256_from_be") _ _ CurrentU256.body callee RlpWrite.U256Value.tupleShape 32 args called capped)
  exact price

/-- Numeric continuations only read memory and mutate their local counters. -/
theorem tail_readonly (kind : Kind) (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code (afterField kind) := by
  cases kind with
  | word=>
    rw [word_shapes.1,word_shapes.2.1,word_shapes.2.2.1,word_shapes.2.2.2.1,word_shapes.2.2.2.2]
    repeat' first
      | apply LocalEffects.sequence
      | apply LocalEffects.conditional
      | apply LocalEffects.declared
      | apply LocalEffects.loop
      | exact LocalEffects.assign code _ _
      | exact LocalEffects.returned code _
      | exact LocalEffects.raised code _ _
      | exact LocalEffects.skip code
  | wide=>
    rw [wide_shape]
    exact LocalEffects.sequence code _ _
      (LocalEffects.conditional code _ _ _ (LocalEffects.raised code _ _) (LocalEffects.skip code))
      (LocalEffects.call_body code none (ofString "u256_from_be") _ _ CurrentU256.body RlpWrite.U256Value.tupleShape
        (CurrentU256.original_code code installed) (CurrentU256.readonly code installed))

/-- Actual slice-array row at a transaction numeric-reader entry. The
parser call arguments are derived from these real cells and bindings. -/
structure Row (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array index pointer length : BitVec 64) : Prop where
  arena : Rlp.LiveArena source
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  pointerMapped : source.memaddrs (array+index*16#64)
  lengthMapped : source.memaddrs (array+index*16#64+8#64)
  pointerStored : source.memory (array+index*16#64)=.word pointer
  lengthStored : source.memory (array+index*16#64+8#64)=.word length
  fits : pointer.toNat+length.toNat<2^64

theorem Row.arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length : BitVec 64}
    (row : Row source array index pointer length) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) TransactionFields.rowArguments=some (Rlp.Header.values pointer length) :=
  TransactionFields.row_arguments source array index pointer length row.arrayCell row.indexCell row.pointerMapped row.lengthMapped row.pointerStored row.lengthStored

theorem Row.call {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length : BitVec 64}
    (row : Row source array index pointer length) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : callee.lookup (ofString "i")=some (.val (.word index))) : Row (callEntryStateHOLFinite source callee) array index pointer length := {
  row with arena:=row.arena.of_frame rfl,arrayCell:=arrayCell,indexCell:=indexCell }

/-- The real three-word scalar-item ABI preserves exactly the same row. -/
theorem scalar_environment {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length maxb : BitVec 64}
    (row : Row source array index pointer length)
    (maxCell : source.locals.lookup (ofString "maxb")=some (.val (.word maxb))) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) fieldArguments=
        some [.val (.word array),.val (.word index),.val (.word maxb)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "tx_scalar_item") [.val (.word array),.val (.word index),.val (.word maxb)]=
        some (TransactionFields.body .scalar,callee,.comb [.one,.one]) ∧ Row (callEntryStateHOLFinite source callee) array index pointer length := by
  obtain ⟨callee,called,arrayCell,indexCell,_calleeMax⟩:=word_triple_environment source.code.lookup (ofString "tx_scalar_item")
    (ofString "arr") (ofString "i") (ofString "maxb") (TransactionFields.body .scalar) (.comb [.one,.one]) array index maxb
    (by decide) (by decide) (by decide) (TransactionFields.original_code .scalar source.code row.arena.code)
  exact ⟨callee,by simp [fieldArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,row.arrayCell,row.indexCell,maxCell],
    called,row.call callee arrayCell indexCell⟩

def tailPrice : Kind→Nat | .word=>8 | .wide=>33

/-- Complete current numeric-reader body: real scalar-item parse, actual
width guard, and every byte-fold or 256-bit conversion outcome. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length maxb : BitVec 64}
    (row : Row source array index pointer length) (maxCell : source.locals.lookup (ofString "maxb")=some (.val (.word maxb))) (kind : Kind) :
    source.clock-(evaluateHOLFiniteState source (body kind)).2.clock≤60*length.toNat+12+tailPrice kind := by
  obtain ⟨callee,args,called,entry⟩:=scalar_environment row maxCell
  have firstPrice:=TransactionFields.body_cost (callEntryStateHOLFinite source callee) .scalar pointer length entry.arena entry.fits entry.arguments
  rw [shapes]
  have price:=ClockCost.scoped_reached_current source "f" (.comb [.one,.one]) (ofString "tx_scalar_item") fieldArguments _
    (TransactionFields.body .scalar) (afterField kind) callee (.comb [.one,.one]) (60*length.toNat+11) (tailPrice kind)
    args called firstPrice (by
      intro child answer normal checked
      obtain ⟨header,payload,flag,valid,valueEq,frame⟩:=TransactionFields.body_pair_normal (callEntryStateHOLFinite source callee) child .scalar
        pointer length (Or.inl rfl) entry.arena entry.fits entry.arguments answer normal
      let resumed:=CallNormal.continuationEntry source child "f" answer
      have fCell : resumed.locals.lookup (ofString "f")=some (pair (pointer+header) payload):=by
        simp [resumed,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq,pair]
      have installed : OriginalCode.Installed resumed.code:=by
        change OriginalCode.Installed child.code
        rw [MemoryMetadata.code frame.metadata]
        exact row.arena.code
      cases kind with
      | word=>exact word_tail_cost resumed (pointer+header) payload fCell
      | wide=>exact wide_tail_cost resumed (pointer+header) payload installed fCell)
  omega

/-- Actual normal numeric returns retain decoded input and every earlier
persistent word; temporary RLP validation scratch alone may change. -/
theorem body_normal_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length maxb : BitVec 64}
    (row : Row source array index pointer length) (maxCell : source.locals.lookup (ofString "maxb")=some (.val (.word maxb)))
    (kind : Kind) (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    Rlp.CurrentItem.Frame source target := by
  obtain ⟨callee,args,called,entry⟩:=scalar_environment row maxCell
  rw [shapes] at normal
  obtain ⟨funded,child,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source target "f" (.comb [.one,.one])
    (ofString "tx_scalar_item") fieldArguments _ (TransactionFields.body .scalar) (afterField kind) callee (.comb [.one,.one]) args called value normal
  have frame:=TransactionFields.body_normal_frame (callEntryStateHOLFinite source callee) child .scalar pointer length entry.arena entry.fits entry.arguments answer bodyRun
  have installed : OriginalCode.Installed child.code:=by rw [MemoryMetadata.code frame.metadata]; exact row.arena.code
  have readonly:=tail_readonly kind child.code installed (CallNormal.continuationEntry source child "f" answer) rfl
  rw [continued] at readonly
  have final : LocalEffects.erase target=LocalEffects.erase child:=by rw [endpoint]; exact readonly
  exact frame.of_erase rfl final

set_option maxRecDepth 100000 in
theorem word_original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "tx_scalar_word")=some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one),(ofString "envcode",.one)],body .word,.one) := by
  have checked:=OriginalCode.indexed code installed 271 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_scalar_word) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_tx_scalar_word,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem wide_original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "tx_scalar_u256")=some ([(ofString "arr",.one),(ofString "i",.one),(ofString "maxb",.one)],body .wide,RlpWrite.U256Value.tupleShape) := by
  have checked:=OriginalCode.indexed code installed 270 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_scalar_u256) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_tx_scalar_u256,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.wide_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.limit_of_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_iteration_saved
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_after_guard_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.wide_tail_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.tail_readonly

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.Row.arguments

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.scalar_environment

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.body_normal_frame

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.word_original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionNumbers.wide_original_code
