import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.ClockCostDeclaredReached
import InitECandidate.Solver.Input.CurrentVerify.TransactionLists
import InitECandidate.Solver.Input.CallPrefixFrameTrace
import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.Input.CallPrefixCommand
import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.Input.ZeroAnyCost
import InitECandidate.Solver.Rlp.CurrentDecodeCall
import InitECandidate.Solver.Input.NoReturnDecision

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Extract the real envelope selector from the unchanged transaction decoder.
The later field decoder remains its actual continuation. -/
def body : ProgHOL 64:=match Guest.Software.guestFn_decode_transaction_rlp with | .function fn=>progToHOL fn.body | _=>.skip
def afterEmpty : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip
def afterByte : ProgHOL 64:=match afterEmpty with | .dec _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterByte with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterZero : ProgHOL 64:=match afterAllocation with | .seq _ rest=>rest | _=>.skip
def afterRawPointer : ProgHOL 64:=match afterZero with | .seq _ rest=>rest | _=>.skip
def envelopeDeclarations : ProgHOL 64:=match afterRawPointer with | .seq _ rest=>rest | _=>.skip
def afterTop : ProgHOL 64:=match envelopeDeclarations with | .dec _ _ _ rest=>rest | _=>.skip
def afterType : ProgHOL 64:=match afterTop with | .dec _ _ _ rest=>rest | _=>.skip
def selectionAndFields : ProgHOL 64:=match afterType with | .dec _ _ _ rest=>rest | _=>.skip
def selection : ProgHOL 64:=match selectionAndFields with | .seq first _=>first | _=>.skip
def afterSelection : ProgHOL 64:=match selectionAndFields with | .seq _ rest=>rest | _=>.skip
def typedTest : ExpHOL 64:=match selection with | .ite test _ _=>test | _=>.const 0#64
def typedSelection : ProgHOL 64:=match selection with | .ite _ yes _=>yes | _=>.skip
def legacyChoice : ProgHOL 64:=match selection with | .ite _ _ no=>no | _=>.skip
def legacyTest : ExpHOL 64:=match legacyChoice with | .ite test _ _=>test | _=>.const 0#64
def typeUpdates : ProgHOL 64:=match typedSelection with | .seq _ rest=>rest | _=>.skip
def decodeArguments (typed : Bool) : List (ExpHOL 64):=
  if typed then [.op .add [localVar "p",.const 1#64],.op .sub [localVar "len",.const 1#64]] else [localVar "p",localVar "len"]
def decodeCall (typed : Bool) : ProgHOL 64:=.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") (decodeArguments typed)

set_option maxRecDepth 100000 in
theorem selection_shapes : selectionAndFields=.seq selection afterSelection ∧
    selection=.ite typedTest typedSelection legacyChoice ∧
    typedSelection=.seq (decodeCall true) typeUpdates ∧
    legacyChoice=.ite legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64)) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp (maxSteps:=1000000) only [afterSelection,typedTest,typedSelection,typeUpdates,legacyChoice,legacyTest,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,decodeCall,decodeArguments,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,localVar,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]

set_option maxRecDepth 100000 in
/-- The actual type/count assignments protect every other caller binding. -/
theorem updates_saved (key : MlS) (notType : key≠ofString "t") (notCount : key≠ofString "nfields") : LocalPrefix key typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | exact LocalPrefix.skip
    | exact LocalPrefix.assign _ _ notType
    | exact LocalPrefix.assign _ _ notCount

set_option maxRecDepth 100000 in
theorem updates_readonly (code) : LocalEffects.Preserves code typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply LocalEffects.sequence
    | apply LocalEffects.conditional
    | exact LocalEffects.skip code
    | exact LocalEffects.assign code _ _

set_option maxRecDepth 100000 in
theorem updates_quiet (code) : QuietClock.Preserves code typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply QuietClock.sequence
    | apply QuietClock.conditional
    | exact QuietClock.skip code
    | exact QuietClock.assign code _ _

/-- Removing the actual type byte preserves the original nonwrapping span.
The nonempty fact is supplied by the decoder's preceding empty guard. -/
theorem typed_extent (pointer length : BitVec 64) (positive : 1≤length.toNat)
    (fits : pointer.toNat+length.toNat<2^64) :
    (pointer+1#64).toNat=pointer.toNat+1 ∧ (length-1#64).toNat=length.toNat-1 ∧
      (pointer+1#64).toNat+(length-1#64).toNat=pointer.toNat+length.toNat := by
  have first : (pointer+1#64).toNat=pointer.toNat+1:=BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; omega)
  have second : (length-1#64).toNat=length.toNat-1:=by
    rw [BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact positive)]
    rfl
  exact ⟨first,second,by omega⟩

theorem decode_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (decodeArguments typed)=
      some (Rlp.Header.values (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length)) := by
  cases typed <;> simp [decodeArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
    pointerCell,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Both actual assigned parser calls cover all stopped outcomes. -/
theorem decode_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (entry : Rlp.CurrentItem.Entry source pointer length) :
    source.clock-(evaluateHOLFiniteState source (decodeCall typed)).2.clock≤60*length.toNat+13 := by
  let start:=if typed then pointer+1#64 else pointer
  let count:=if typed then length-1#64 else length
  have args:=decode_arguments source pointer length typed entry.pointerCell entry.lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape start count
    (Rlp.Decode.original_code source.code entry.arena.code)
  have extent : start.toNat+count.toNat<2^64:=by
    cases typed
    · exact entry.fits
    · change (pointer+1#64).toNat+(length-1#64).toNat<2^64
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.2]
      exact entry.fits
  have countBound : count.toNat≤length.toNat:=by
    cases typed
    · exact Nat.le_refl _
    · change (length-1#64).toNat≤length.toNat
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.1]
      omega
  have priced:=ClockCost.assigned_current source (some (.local,ofString "top")) (ofString "rlp_decode_fully") (decodeArguments typed)
    _ Rlp.Decode.body callee Rlp.Item.resultShape (60*count.toNat+12) args called
    (Rlp.CurrentDecode.body_cost (callEntryStateHOLFinite source callee) start count pointerLocal lengthLocal (entry.arena.of_frame rfl) extent entry.arena.code)
  change source.clock-(evaluateHOLFiniteState source (decodeCall typed)).2.clock≤60*count.toNat+12+1 at priced
  omega

/-- The actual assigned return supplies a complete parse and its real top
binding, while protecting persistent input and original runtime metadata. -/
theorem decode_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (normal : evaluateHOLFiniteState source (decodeCall typed)=(none,target)) :
    ∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      target.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source target ∧
      ∀ key,key≠ofString "top"→target.locals.lookup key=source.locals.lookup key := by
  let start:=if typed then pointer+1#64 else pointer
  let count:=if typed then length-1#64 else length
  have args:=decode_arguments source pointer length typed entry.pointerCell entry.lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape start count
    (Rlp.Decode.original_code source.code entry.arena.code)
  obtain ⟨funded,values,actual,locals,shape,child,answer,arguments,lookup,run,checked,endpoint⟩:=
    CallNormal.local_data source target (ofString "top") (ofString "rlp_decode_fully") (decodeArguments typed) normal
  have valuesEq:=Option.some.inj (arguments.symm.trans args)
  rw [valuesEq,called] at lookup
  have same:=(Option.some.inj lookup).symm
  have actualEq : actual=Rlp.Decode.body:=congrArg Prod.fst same
  have localsEq : locals=callee:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [actualEq,localsEq] at run
  have extent : start.toNat+count.toNat<2^64:=by
    cases typed
    · exact entry.fits
    · change (pointer+1#64).toNat+(length-1#64).toNat<2^64
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.2]
      exact entry.fits
  obtain ⟨complete,frame,price⟩:=Rlp.CurrentDecode.body_normal (callEntryStateHOLFinite source callee) child start count
    pointerLocal lengthLocal (entry.arena.of_frame rfl) extent entry.arena.code answer run
  refine ⟨answer,complete,?_,frame.of_erase rfl (by rw [endpoint]; rfl),?_⟩
  · rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro key other
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]

/-- At most one complete RLP parse occurs in the actual type selector. -/
theorem selection_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) :
    source.clock-(evaluateHOLFiniteState source selection).2.clock≤60*length.toNat+13 := by
  rw [selection_shapes.2.1]
  have typedPrice : source.clock-(evaluateHOLFiniteState source typedSelection).2.clock≤60*length.toNat+13:=by
    rw [selection_shapes.2.2.1]
    have priced:=ClockCost.sequence_current source (decodeCall true) typeUpdates (60*length.toNat+13) 0
      (decode_call_cost source pointer length true entry) (ClockCost.of_quiet source.code typeUpdates (updates_quiet source.code))
    simpa only [Nat.add_zero] using priced
  have legacyPrice:=ClockCost.conditional_current source legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64))
    (60*length.toNat+13) 0 (decode_call_cost source pointer length false entry) (ClockCost.raised source.code _ _ source rfl)
  rw [←selection_shapes.2.2.2] at legacyPrice
  simpa only [Nat.max_zero,Nat.max_self] using ClockCost.conditional_current source typedTest typedSelection legacyChoice
    (60*length.toNat+13) (60*length.toNat+13) typedPrice (by simpa only [Nat.max_zero] using legacyPrice)


/-- Real normal selection retains one complete parse within the original
input extent. Type/count assignments do not overwrite the returned top item. -/
theorem selection_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (normal : evaluateHOLFiniteState source selection=(none,target)) :
    ∃ typed : Bool,∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      target.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source target ∧
      ∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→target.locals.lookup key=source.locals.lookup key := by
  rw [selection_shapes.2.1] at normal
  rcases conditional_none source target typedTest typedSelection legacyChoice normal with typedRun|legacyRun
  · rw [selection_shapes.2.2.1] at typedRun
    obtain ⟨middle,decodeRun,updatesRun⟩:=sequence_none source target (decodeCall true) typeUpdates typedRun
    obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source middle pointer length true entry decodeRun
    have physical:=updates_readonly middle.code middle rfl
    rw [updatesRun] at physical
    have retained:=(updates_saved (ofString "top") (by decide) (by decide)).summary middle
    rw [updatesRun] at retained
    refine ⟨true,answer,complete,retained.1 rfl |>.trans topCell,(Rlp.CurrentItem.Frame.of_readonly physical).trans frame,?_⟩
    intro key notTop notType notCount
    have kept:=(updates_saved key notType notCount).summary middle
    rw [updatesRun] at kept
    exact (kept.1 rfl).trans (saved key notTop)
  · rw [selection_shapes.2.2.2] at legacyRun
    rcases conditional_none source target legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64)) legacyRun with decodeRun|rejected
    · obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source target pointer length false entry decodeRun
      exact ⟨false,answer,complete,topCell,frame,fun key notTop _ _=>saved key notTop⟩
    · exact False.elim (raise_ne_none source (ofString "TxErr") (.const 2#64) (congrArg Prod.fst rejected))


def emptyGuard : ProgHOL 64:=.ite (.cmp .equal (localVar "len") (.const 0#64)) (.raise (ofString "TxErr") (.const 1#64)) .skip
def listGuard : ProgHOL 64:=TransactionFields.rejectUnequal (.rfield 0 (localVar "top")) (.const 1#64) 3#64

theorem empty_shape : body=.seq emptyGuard afterEmpty := by
  simp only [body,emptyGuard,afterEmpty,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

/-- Nonempty input is derived from the actual preceding guard, including
cases where its exception shape is missing or malformed. -/
theorem nonempty_of_guard (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source emptyGuard=(none,target)) : 1≤length.toNat := by
  by_contra empty
  have zero : length=0#64:=BitVec.eq_of_toNat_eq (by change length.toNat=0; omega)
  have read : eval source (.cmp .equal (localVar "len") (.const 0#64))=some (.val (.word 1#64)):=by
    simp [eval,evalHOLExact,toExact,localVar,lengthCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [emptyGuard,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at read
  rw [read] at normal
  exact raise_ne_none source (ofString "TxErr") (.const 1#64) (congrArg Prod.fst normal)

/-- The real reached list guard establishes a list payload contained in
its complete selected input. No payload or later conversion is assumed. -/
theorem payload_of_guard (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer) (fits : pointer.toNat+length.toNat<2^64)
    (topCell : source.locals.lookup (ofString "top")=some answer)
    (normal : evaluateHOLFiniteState source listGuard=(none,target)) :
    ∃ header payload,answer=Rlp.Item.result pointer header payload 1#64 ∧ 1≤header.toNat ∧
      (pointer+header).toNat=pointer.toNat+header.toNat ∧ (pointer+header).toNat+payload.toNat=pointer.toNat+length.toNat ∧
      payload.toNat≤length.toNat ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
        [.rfield 1 (localVar "top"),.rfield 2 (localVar "top")]=some (Rlp.Header.values (pointer+header) payload) := by
  obtain ⟨header,payload,flag,same,small,positive,total,binary,listHeader⟩:=complete
  have tagRead : eval source (.rfield 0 (localVar "top"))=some (.val (.word flag)):=by
    simp [eval,evalHOLExact,toExact,localVar,topCell,same,Rlp.Item.result]
  have flagEq:=TransactionFields.reject_unequal_normal source target (.rfield 0 (localVar "top")) (.const 1#64) 3#64 flag 1#64 tagRead rfl normal
  subst flag
  have added : (pointer+header).toNat=pointer.toNat+header.toNat:=BitVec.toNat_add_of_lt (by omega)
  refine ⟨header,payload,same,listHeader rfl,added,by omega,by omega,?_⟩
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,topCell,same,Rlp.Item.result,Rlp.Header.values]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_transaction_rlp")=some ([(ofString "p",.one),(ofString "len",.one)],body,.one) := by
  have checked:=OriginalCode.indexed code installed 279 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_transaction_rlp) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.Software.guestFn_decode_transaction_rlp,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked


def afterTypeStore : ProgHOL 64:=match afterSelection with | .seq _ rest=>rest | _=>.skip
def afterListGuard : ProgHOL 64:=match afterTypeStore with | .seq _ rest=>rest | _=>.skip
def afterSlices : ProgHOL 64:=match afterListGuard with | .decCall _ _ _ _ rest=>rest | _=>.skip
def sliceArguments : List (ExpHOL 64):=[.rfield 1 (localVar "top"),.rfield 2 (localVar "top")]

set_option maxRecDepth 100000 in
theorem continuation_shapes : afterSelection=.seq (.store (.op .add [localVar "tx",.const 0#64]) (localVar "t")) afterTypeStore ∧
    afterTypeStore=.seq listGuard afterListGuard ∧
    afterListGuard=.decCall (ofString "lst") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices := by
  simp (maxSteps:=1000000) only [afterTypeStore,afterListGuard,afterSlices,afterSelection,listGuard,TransactionFields.rejectUnequal,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    sliceArguments,Rlp.Slices.resultShape,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  trivial

theorem decode_call_no_return (typed : Bool) : NoReturn.Never (decodeCall typed) := by
  have safe : LocalPrefix (ofString "p") (decodeCall typed):=by
    unfold decodeCall
    exact .call (some (ofString "top")) _ _ (by intro name same; cases same; decide)
  intro F source value
  exact (safe.summary source).2 value

theorem selection_no_return : NoReturn.Never selection := by
  rw [selection_shapes.2.1]
  apply NoReturn.conditional
  · rw [selection_shapes.2.2.1]
    apply NoReturn.sequence _ _ (decode_call_no_return true)
    intro F source value
    exact ((updates_saved (ofString "p") (by decide) (by decide)).summary source).2 value
  · rw [selection_shapes.2.2.2]
    exact NoReturn.conditional _ _ _ (decode_call_no_return false) (NoReturn.raise _ _)

/-- The later field suffix is charged only after the same actual selector
returns a complete parse. Rejections, malformed reads and short clocks stay
in the selector's all-outcome allowance. -/
theorem fields_reached_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) (tailPrice : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ typed : Bool,∀ answer,
      Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer→
      current.locals.lookup (ofString "top")=some answer→Rlp.CurrentItem.Frame source current→
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=source.locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current afterSelection).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source selectionAndFields).2.clock≤60*length.toNat+13+tailPrice := by
  rw [selection_shapes.1]
  apply ClockCost.sequence_reached_current source selection afterSelection (60*length.toNat+13) tailPrice (selection_cost source pointer length entry)
  intro current normal
  obtain ⟨typed,answer,complete,topCell,frame,saved⟩:=selection_normal source current pointer length entry normal
  exact tail current typed answer complete topCell frame saved

/-- A genuine enclosing return reaches the real field continuation with
its observed parse and memory frame; no future normal return is postulated. -/
theorem fields_returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source selectionAndFields=(some (.returned value),target)) :
    ∃ current,∃ typed : Bool,∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      current.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source current ∧
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=source.locals.lookup key) ∧
      evaluateHOLFiniteState current afterSelection=(some (.returned value),target) := by
  rw [selection_shapes.1] at normal
  obtain ⟨current,selected,continued⟩:=sequence_returned source target selection afterSelection value (selection_no_return source) normal
  obtain ⟨typed,answer,complete,topCell,frame,saved⟩:=selection_normal source current pointer length entry selected
  exact ⟨current,typed,answer,complete,topCell,frame,saved,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_saved
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_quiet
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.typed_extent
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.empty_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonempty_of_guard
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.payload_of_guard
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.continuation_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_no_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_no_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_reached_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_returned


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def zeroCall : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "tx",.const 400#64]
def rawPointerStore : ProgHOL 64:=.store (.op .add [localVar "tx",.const 384#64]) (localVar "p")
def rawLengthStore : ProgHOL 64:=.store (.op .add [localVar "tx",.const 392#64]) (localVar "len")
def zeroTop : ExpHOL 64:=.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]
def setupActions : List CallPrefix.Action:=[
  .command emptyGuard,.declare (ofString "b0") .one (.loadByte (localVar "p")),
  .scoped (ofString "tx") .one (ofString "alloc") [.const 400#64],
  .command zeroCall,.command rawPointerStore,.command rawLengthStore,
  .declare (ofString "top") Rlp.Item.resultShape zeroTop,.declare (ofString "t") .one (.const 0#64),
  .declare (ofString "nfields") .one (.const 9#64)]

set_option maxRecDepth 100000 in
theorem setup_shape : body=CallPrefix.program setupActions selectionAndFields := by
  simp (maxSteps:=1000000) only [body,setupActions,CallPrefix.program,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,emptyGuard,zeroCall,rawPointerStore,rawLengthStore,zeroTop,Rlp.Item.resultShape,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

/-- Fixed setup price, even when the real input, allocation or zeroing
stops. No pointer alignment or successful future call is needed for this cost. -/
theorem setup_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code (CallPrefix.program setupActions .skip) 515 := by
  have tail : ClockCost.Bound code (CallPrefix.program (setupActions.drop 4) .skip) 0:=by
    unfold setupActions
    simp only [List.drop,CallPrefix.program]
    apply ClockCost.sequence _ _ _ 0 0 (ClockCost.store _ _ _)
    apply ClockCost.sequence _ _ _ 0 0 (ClockCost.store _ _ _)
    apply ClockCost.declared
    apply ClockCost.declared
    apply ClockCost.declared
    exact ClockCost.skip code
  have clearing : ClockCost.Bound code zeroCall 513:=by
    intro source codeEq
    have actual:=ZeroAny.dynamic_call_cost source (localVar "tx") 400 (by decide) (by rw [codeEq]; exact Zero.original_code code installed)
    exact actual
  have afterAlloc:=ClockCost.sequence code zeroCall (CallPrefix.program (setupActions.drop 4) .skip) 513 0 clearing tail
  have allocating:=PersistentAlloc.scoped_price code installed (ofString "tx") .one [.const 400#64] _ 513 (by simpa only [Nat.add_zero] using afterAlloc)
  have declared:=ClockCost.declared code (ofString "b0") .one (.loadByte (localVar "p")) _ 515 allocating
  have guard : ClockCost.Bound code emptyGuard 0:=ClockCost.of_quiet code emptyGuard
    (PureDecision.quiet (PureDecision.ite _ (.raised _ _) .skip) code)
  have priced:=ClockCost.sequence code emptyGuard _ 0 515 guard declared
  simpa only [setupActions,CallPrefix.program,Nat.zero_add,List.drop] using priced

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap byte : BitVec 64) :=
  setVarHOLFinite (ofString "tx") (.val (.word heap)) (PersistentAlloc.post {bind source "b0" byte with clock:=source.clock-1} heap 400#64)
def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap byte : BitVec 64) :=
  {allocated source heap byte with
    memory:=Zero.finalMemory (allocated source heap byte).memory heap 400
    clock:=(allocated source heap byte).clock-(Zero.price 400+1)}
def rawStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) :=
  {cleared source heap byte with memory:=StoreWord.put (StoreWord.put (cleared source heap byte).memory (heap+384#64) pointer) (heap+392#64) length}
def selectionEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) :=
  bind (bind (setVarHOLFinite (ofString "top") (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)])
    (rawStored source pointer length heap byte)) "t" 0#64) "nfields" 9#64

theorem allocated_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap byte : BitVec 64) :
    (allocated source heap byte).locals.lookup (ofString "tx")=some (.val (.word heap)) ∧
      ∀ key,key≠ofString "tx"→key≠ofString "b0"→(allocated source heap byte).locals.lookup key=source.locals.lookup key := by
  constructor
  · simp [allocated,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro key notTx notByte
    simp [allocated,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notTx,Ne.symm notByte]

/-- The same reached setup trace supplies the actual byte, successful
allocation room, zeroed record and exact initialized selector state. -/
theorem setup_execution (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap)
    (execution : CallPrefix.Execution source setupActions target) :
    ∃ byte : BitVec 64,byte.toNat<256 ∧ 1≤length.toNat ∧ heap.toNat+400≤2952790016 ∧
      target=selectionEntry source pointer length heap byte := by
  unfold setupActions at execution
  obtain ⟨guarded,guardRun,afterGuard⟩:=execution.command_next emptyGuard _
  have positive:=nonempty_of_guard source guarded length entry.lengthCell guardRun
  have unchanged:=((show PureGuard emptyGuard from .ite _ (.raise _ _) .skip).summary source).1
  rw [guardRun] at unchanged
  have guardedEq : guarded=source:=unchanged rfl
  rw [guardedEq] at afterGuard
  cases afterGuard with
  | step declaration afterByteTrace=>
    cases declaration with
    | declare _ _ _ value read checked=>
      obtain ⟨byte,byteEq,byteSmall⟩:=byte_expression_value source (localVar "p") value read
      rw [byteEq] at afterByteTrace
      let byteState:=bind source "b0" byte
      have byteHeap : byteState.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=entry.heapCell
      have args : evalListHOLFinite byteState (h:=fun query=>Classical.propDecidable (byteState.memaddrs query)) [.const 400#64]=some (PersistentAlloc.values 400#64):=rfl
      obtain ⟨room,afterAllocTrace⟩:=afterByteTrace.alloc_next (source:=byteState) (ofString "tx") [.const 400#64] heap 400#64 _ entry.arena.code args byteHeap entry.heapBound
      change CallPrefix.Execution (allocated source heap byte) _ target at afterAllocTrace
      have roomNat : heap.toNat+400≤2952790016:=room
      have arena : AllocatedBytes.Arena heap 400:=⟨entry.heapArena.lower,by omega⟩
      obtain ⟨clearedActual,zeroRun,afterZeroTrace⟩:=afterAllocTrace.command_next zeroCall _
      have zeroArgs : evalListHOLFinite (allocated source heap byte) (h:=fun query=>Classical.propDecidable ((allocated source heap byte).memaddrs query))
          [localVar "tx",.const 400#64]=some (Zero.values heap 400):=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,(allocated_locals source heap byte).1,Zero.values]
      have zeroCode:=Zero.original_code source.code entry.arena.code
      obtain ⟨funded,clearedEq⟩:=Zero.call_normal (allocated source heap byte) clearedActual [localVar "tx",.const 400#64] heap 400 zeroArgs zeroCode
        (by decide) (by decide) entry.heapAligned (by
          intro offset inside divisible
          exact AllocatedBytes.word_mapped (allocated source heap byte) heap 400 offset entry.arena.domain arena (by omega) entry.heapAligned divisible) zeroRun
      change clearedActual=cleared source heap byte at clearedEq
      rw [clearedEq] at afterZeroTrace
      obtain ⟨pointerStored,pointerRun,afterPointerTrace⟩:=afterZeroTrace.command_next rawPointerStore _
      have txCell : (cleared source heap byte).locals.lookup (ofString "tx")=some (.val (.word heap)):=(allocated_locals source heap byte).1
      have pCell : (cleared source heap byte).locals.lookup (ofString "p")=some (.val (.word pointer)):=
        ((allocated_locals source heap byte).2 _ (by decide) (by decide)).trans entry.pointerCell
      have destination : eval (cleared source heap byte) (.op .add [localVar "tx",.const 384#64])=some (.val (.word (heap+384#64))):=by
        simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,txCell,valueIsWord,valueWord,wordOpHOL,wordOp]
      have pointerRead : eval (cleared source heap byte) (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,toExact,localVar,pCell]
      obtain ⟨mapped,pointerEq⟩:=word_store_normal (cleared source heap byte) pointerStored _ _ (heap+384#64) pointer destination pointerRead pointerRun
      rw [pointerEq] at afterPointerTrace
      obtain ⟨lengthStored,lengthRun,afterLengthTrace⟩:=afterPointerTrace.command_next rawLengthStore _
      let pointerState:={cleared source heap byte with memory:=StoreWord.put (cleared source heap byte).memory (heap+384#64) pointer}
      have txAgain : pointerState.locals.lookup (ofString "tx")=some (.val (.word heap)):=txCell
      have lengthCell : pointerState.locals.lookup (ofString "len")=some (.val (.word length)):=
        ((allocated_locals source heap byte).2 _ (by decide) (by decide)).trans entry.lengthCell
      have secondDestination : eval pointerState (.op .add [localVar "tx",.const 392#64])=some (.val (.word (heap+392#64))):=by
        simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,txAgain,valueIsWord,valueWord,wordOpHOL,wordOp]
      have lengthRead : eval pointerState (localVar "len")=some (.val (.word length)):=by simp [eval,evalHOLExact,toExact,localVar,lengthCell]
      obtain ⟨mappedAgain,lengthEq⟩:=word_store_normal pointerState lengthStored _ _ (heap+392#64) length secondDestination lengthRead lengthRun
      rw [lengthEq] at afterLengthTrace
      change CallPrefix.Execution (rawStored source pointer length heap byte) _ target at afterLengthTrace
      have topRead : eval (rawStored source pointer length heap byte) zeroTop=some (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]):=rfl
      have topTrace:=afterLengthTrace.declare_next _ topRead
      have typeTrace:=topTrace.declare_next (.val (.word 0#64)) rfl
      have countTrace:=typeTrace.declare_next (.val (.word 9#64)) rfl
      cases countTrace
      exact ⟨byte,byteSmall,positive,roomNat,rfl⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.allocated_locals
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_execution


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack PanSemStateFiniteExact WitnessRadix

set_option maxHeartbeats 1000000 in
/-- Every real aligned word of the actual cleared400-byte record is zero.
No assumption about its previous contents is used. -/
theorem zero_record_word (memory : WordWrites.Memory) (heap : BitVec 64) (index : Nat) (inside : index<50) :
    Zero.finalMemory memory heap 400 (heap+BitVec.ofNat 64 (8*index))=.word 0#64 := by
  have alternatives : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 ∨ index=6 ∨ index=7 ∨ index=8 ∨ index=9 ∨ index=10 ∨ index=11 ∨ index=12 ∨ index=13 ∨ index=14 ∨ index=15 ∨ index=16 ∨ index=17 ∨ index=18 ∨ index=19 ∨ index=20 ∨ index=21 ∨ index=22 ∨ index=23 ∨ index=24 ∨ index=25 ∨ index=26 ∨ index=27 ∨ index=28 ∨ index=29 ∨ index=30 ∨ index=31 ∨ index=32 ∨ index=33 ∨ index=34 ∨ index=35 ∨ index=36 ∨ index=37 ∨ index=38 ∨ index=39 ∨ index=40 ∨ index=41 ∨ index=42 ∨ index=43 ∨ index=44 ∨ index=45 ∨ index=46 ∨ index=47 ∨ index=48 ∨ index=49 := by omega
  rcases alternatives with same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same
  all_goals subst index; simp [Zero.finalMemory,Zero.memory32,Zero.memoryWord,Copy32.memory,Copy32.writes,WordWrites.write,StoreWord.put,BitVec.add_assoc]

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.zero_record_word


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem selection_entry_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) (key : MlS)
    (notTop : key≠ofString "top") (notType : key≠ofString "t") (notCount : key≠ofString "nfields") :
    (selectionEntry source pointer length heap byte).locals.lookup key=(allocated source heap byte).locals.lookup key := by
  simp [selectionEntry,rawStored,cleared,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    Ne.symm notTop,Ne.symm notType,Ne.symm notCount]

/-- Earlier persistent words survive the actual allocation, full zeroing
and both raw metadata stores; only the fresh transaction record is changed. -/
theorem selection_entry_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (room : heap.toNat+400≤2952790016) :
    PersistentNormalFrame source (selectionEntry source pointer length heap byte) heap := by
  have allocatedFrame:=(PersistentAlloc.post_persistent_frame source heap 400#64 entry.heapArena room).of_erase
    source (PersistentAlloc.post source heap 400#64) source (allocated source heap byte) heap rfl rfl
  apply allocatedFrame.after_memory source (allocated source heap byte) (selectionEntry source pointer length heap byte) heap rfl
  intro query before
  have firstNumber : (heap+384#64).toNat=heap.toNat+384:=BitVec.toNat_add_of_lt (by change heap.toNat+384<2^64; omega)
  have secondNumber : (heap+392#64).toNat=heap.toNat+392:=BitVec.toNat_add_of_lt (by change heap.toNat+392<2^64; omega)
  have firstDifferent : query≠heap+384#64:=by intro same; have numeric:=congrArg BitVec.toNat same; omega
  have secondDifferent : query≠heap+392#64:=by intro same; have numeric:=congrArg BitVec.toNat same; omega
  change StoreWord.put (StoreWord.put (Zero.finalMemory (allocated source heap byte).memory heap 400) (heap+384#64) pointer) (heap+392#64) length query=(allocated source heap byte).memory query
  simp only [StoreWord.put,if_neg firstDifferent,if_neg secondDifferent]
  apply Zero.final_memory_away
  intro offset inside same
  have number:=byteAddress_toNat heap offset (by omega)
  have numeric:=congrArg BitVec.toNat same
  omega

/-- The observed room supplies the bounded current heap and live parser
entry after setup, rather than an assumed next allocation or parser success. -/
def selection_entry_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (room : heap.toNat+400≤2952790016) :
    BlobHashes.Entry (selectionEntry source pointer length heap byte) pointer length (PersistentAlloc.rounded heap 400#64) := by
  have guards:=PersistentAlloc.guards heap 400#64 room
  have frame:=selection_entry_frame source pointer length heap byte entry room
  have live : Rlp.LiveArena (selectionEntry source pointer length heap byte):=
    entry.arena.of_cursors rfl rfl (frame.globals _ (by decide)) (frame.globals _ (by decide))
  have grows : heap.toNat+400≤(PersistentAlloc.rounded heap 400#64).toNat:=guards.2.2.1
  exact {
    arena:=live
    pointerCell:=((selection_entry_saved source pointer length heap byte _ (by decide) (by decide) (by decide)).trans
      ((allocated_locals source heap byte).2 _ (by decide) (by decide))).trans entry.pointerCell
    lengthCell:=((selection_entry_saved source pointer length heap byte _ (by decide) (by decide) (by decide)).trans
      ((allocated_locals source heap byte).2 _ (by decide) (by decide))).trans entry.lengthCell
    heapCell:=by simp [selectionEntry,rawStored,cleared,allocated,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=entry.heapArena.lower; omega,by have upper:=guards.2.2.2.1; omega⟩
    heapBound:=guards.2.2.2.1
    heapAligned:=guards.2.2.2.2
    inputBefore:=by have inputBefore:=entry.inputBefore; omega }

theorem selection_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) :
    (selectionEntry source pointer length heap byte).locals.lookup (ofString "tx")=some (.val (.word heap)) ∧
    (selectionEntry source pointer length heap byte).locals.lookup (ofString "b0")=some (.val (.word byte)) ∧
    (selectionEntry source pointer length heap byte).locals.lookup (ofString "t")=some (.val (.word 0#64)) ∧
    (selectionEntry source pointer length heap byte).locals.lookup (ofString "nfields")=some (.val (.word 9#64)) ∧
    (selectionEntry source pointer length heap byte).locals.lookup (ofString "top")=some (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]) := by
  refine ⟨(selection_entry_saved source pointer length heap byte _ (by decide) (by decide) (by decide)).trans (allocated_locals source heap byte).1,?_,?_,?_,?_⟩
  · rw [selection_entry_saved source pointer length heap byte _ (by decide) (by decide) (by decide)]
    simp [allocated,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "tx"≠ofString "b0" from by decide]
  · unfold selectionEntry
    exact (bind_lookup_other _ "nfields" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _
  · simp [selectionEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "nfields"≠ofString "top" from by decide,show ofString "t"≠ofString "top" from by decide]

theorem selection_entry_raw (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) :
    (selectionEntry source pointer length heap byte).memory (heap+384#64)=.word pointer ∧
      (selectionEntry source pointer length heap byte).memory (heap+392#64)=.word length := by
  simp [selectionEntry,rawStored,QueryBranch.bind,setVarHOLFinite,StoreWord.put]

/-- All ordinary fields are initially zero; raw pointer and length occupy
only the last two words of the actual400-byte record. -/
theorem selection_entry_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) (index : Nat) (inside : index<48) :
    (selectionEntry source pointer length heap byte).memory (heap+BitVec.ofNat 64 (8*index))=.word 0#64 := by
  have small : 8*index<384:=by omega
  have firstDifferent : heap+BitVec.ofNat 64 (8*index)≠heap+384#64:=by
    intro same
    have numeric:=congrArg BitVec.toNat ((BitVec.add_right_inj heap).mp same)
    change (8*index)%2^64=384 at numeric
    rw [Nat.mod_eq_of_lt (by omega)] at numeric
    omega
  have secondDifferent : heap+BitVec.ofNat 64 (8*index)≠heap+392#64:=by
    intro same
    have numeric:=congrArg BitVec.toNat ((BitVec.add_right_inj heap).mp same)
    change (8*index)%2^64=392 at numeric
    rw [Nat.mod_eq_of_lt (by omega)] at numeric
    omega
  change StoreWord.put (StoreWord.put (Zero.finalMemory (allocated source heap byte).memory heap 400) (heap+384#64) pointer) (heap+392#64) length (heap+BitVec.ofNat 64 (8*index))=.word 0#64
  simp only [StoreWord.put,if_neg firstDifferent,if_neg secondDifferent]
  exact zero_record_word _ heap index (by omega)

/-- Every actual body outcome stops in setup or reaches its genuine
initialized selector entry, retaining scope metadata and the original input. -/
theorem setup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤515 ∨ ∃ byte inner,byte.toNat<256 ∧ 1≤length.toNat ∧ heap.toNat+400≤2952790016 ∧
      PersistentNormalFrame source (selectionEntry source pointer length heap byte) heap ∧
      Nonempty (BlobHashes.Entry (selectionEntry source pointer length heap byte) pointer length (PersistentAlloc.rounded heap 400#64)) ∧
      (selectionEntry source pointer length heap byte).clock≤source.clock ∧
      source.clock-(selectionEntry source pointer length heap byte).clock≤515 ∧
      CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState (selectionEntry source pointer length heap byte) selectionAndFields=(outcome,inner) := by
  rw [setup_shape] at run
  rcases CallPrefix.priced_frame_trace source post setupActions selectionAndFields 515 (setup_cost source.code entry.arena.code source rfl) outcome run with stopped|reached
  · exact Or.inl stopped.1
  · obtain ⟨current,inner,execution,forward,price,scope,continued⟩:=reached
    obtain ⟨byte,byteSmall,positive,room,endpoint⟩:=setup_execution source current pointer length heap entry execution
    rw [endpoint] at forward price continued
    exact Or.inr ⟨byte,inner,byteSmall,positive,room,selection_entry_frame source pointer length heap byte entry room,
      ⟨selection_entry_ready source pointer length heap byte entry room⟩,forward,price,scope,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_saved
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_ready
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_raw
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_zero
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_trace


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem setup_no_return : NoReturn.Never (CallPrefix.program setupActions .skip) := by
  simp only [setupActions,CallPrefix.program,emptyGuard,zeroCall,rawPointerStore,rawLengthStore]
  repeat' first
    | apply NoReturn.sequence
    | apply NoReturn.declared
    | apply NoReturn.scoped_call
    | apply NoReturn.conditional
    | exact NoReturn.store _ _
    | exact NoReturn.ignored_call _ _
    | exact NoReturn.raise _ _
    | exact NoReturn.skip

/-- Any genuine decoder return must pass the actual setup. Its observed
allocation room and initialized continuation are derived from that same run. -/
theorem setup_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ byte : BitVec 64,∃ inner,byte.toNat<256 ∧ 1≤length.toNat ∧ heap.toNat+400≤2952790016 ∧
      PersistentNormalFrame source (selectionEntry source pointer length heap byte) heap ∧
      evaluateHOLFiniteState (selectionEntry source pointer length heap byte) selectionAndFields=(some (.returned value),inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rw [setup_shape] at normal
  obtain ⟨current,inner,execution,continued,clock,physical⟩:=CallPrefix.normal_frame_trace source post setupActions selectionAndFields value setup_no_return normal
  obtain ⟨byte,small,positive,room,endpoint⟩:=setup_execution source current pointer length heap entry execution
  rw [endpoint] at continued
  exact ⟨byte,inner,small,positive,room,selection_entry_frame source pointer length heap byte entry room,continued,clock,physical⟩

/-- The actual setup-derived live state meets the already checked selector
entry, including nonempty input and its nonwrapping input extent. -/
def selected_parser_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (positive : 1≤length.toNat) (room : heap.toNat+400≤2952790016) :
    Rlp.CurrentItem.Entry (selectionEntry source pointer length heap byte) pointer length := by
  let ready:=selection_entry_ready source pointer length heap byte entry room
  exact ⟨ready.pointerCell,ready.lengthCell,ready.arena,positive,by
    have before:=ready.inputBefore
    have bounded:=ready.heapBound
    omega⟩

/-- All stopped setup paths retain their fixed allowance. Later work is
charged only at the same actual initialized selector state. -/
theorem body_reached_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (tailPrice : Nat)
    (tail : ∀ byte : BitVec 64,byte.toNat<256→1≤length.toNat→heap.toNat+400≤2952790016→
      (selectionEntry source pointer length heap byte).clock-(evaluateHOLFiniteState (selectionEntry source pointer length heap byte) selectionAndFields).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤515+tailPrice := by
  let output:=evaluateHOLFiniteState source body
  rcases setup_trace source output.2 pointer length heap entry output.1 rfl with stopped|reached
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨byte,inner,small,positive,room,frame,ready,forward,price,scope,continued⟩:=reached
    have allowance:=tail byte small positive room
    rw [continued] at allowance
    change (selectionEntry source pointer length heap byte).clock-inner.clock≤tailPrice at allowance
    have suffixForward:=evaluateHOLFiniteState_clock_le (selectionEntry source pointer length heap byte) selectionAndFields
    rw [continued] at suffixForward
    change inner.clock≤(selectionEntry source pointer length heap byte).clock at suffixForward
    have clock:=scope.clock
    change output.2.clock=inner.clock at clock
    change source.clock-output.2.clock≤515+tailPrice
    rw [clock]
    omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_no_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_returned
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selected_parser_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_reached_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def fieldCount (tag : BitVec 64) : BitVec 64:=
  if tag=4#64 then 13#64 else if tag=3#64 then 14#64 else if tag=2#64 then 12#64 else if tag=1#64 then 11#64 else 9#64

def countStep (tag count : BitVec 64) : ProgHOL 64:=
  .ite (.cmp .equal (localVar "t") (.const tag)) (.assign .local (ofString "nfields") (.const count)) .skip
def countUpdates : ProgHOL 64:=match typeUpdates with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem type_shapes : typeUpdates=.seq (.assign .local (ofString "t") (localVar "b0")) countUpdates ∧
    countUpdates=.seq (countStep 1#64 11#64) (.seq (countStep 2#64 12#64) (.seq (countStep 3#64 14#64) (countStep 4#64 13#64))) ∧
    typedTest=.op .and [
      .cmp .notEqual (.const 0#64) (.cmp .notLower (localVar "b0") (.const 1#64)),
      .cmp .notEqual (.const 0#64) (.cmp .notLower (.const 4#64) (localVar "b0"))] := by
  simp (maxSteps:=1000000) only [typeUpdates,countUpdates,countStep,typedTest,typedSelection,selection,selectionAndFields,
    afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem field_count_bounds (tag : BitVec 64) : 9≤(fieldCount tag).toNat ∧ (fieldCount tag).toNat≤14 := by
  unfold fieldCount
  split_ifs <;> decide

/-- A real normally continuing count test either assigns its literal count
or retains the previous count, while preserving the actual type binding. -/
theorem count_step_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (byte tag count previous : BitVec 64)
    (typeCell : source.locals.lookup (ofString "t")=some (.val (.word byte)))
    (countCell : source.locals.lookup (ofString "nfields")=some (.val (.word previous)))
    (normal : evaluateHOLFiniteState source (countStep tag count)=(none,target)) :
    target.locals.lookup (ofString "t")=some (.val (.word byte)) ∧
      target.locals.lookup (ofString "nfields")=some (.val (.word (if byte=tag then count else previous))) := by
  have observed : eval source (.cmp .equal (localVar "t") (.const tag))=some (.val (.word (if byte=tag then 1#64 else 0#64))):=by
    simp [eval,evalHOLExact,toExact,localVar,typeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [countStep,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  by_cases same : byte=tag
  · rw [if_pos same] at normal
    change evaluateHOLFiniteState source (.assign .local (ofString "nfields") (.const count))=(none,target) at normal
    have endpoint:=assign_none source target "nfields" (.const count) count rfl normal
    rw [endpoint]
    exact ⟨(bind_lookup_other source "nfields" "t" count (by decide)).trans typeCell,by simpa only [if_pos same] using bind_lookup_same source "nfields" count⟩
  · rw [if_neg same] at normal
    change evaluateHOLFiniteState source .skip=(none,target) at normal
    rw [evaluateHOLFiniteState_skip] at normal
    have endpoint : source=target:=congrArg Prod.snd normal
    rw [←endpoint]
    exact ⟨typeCell,by simpa only [if_neg same] using countCell⟩

/-- The actual four count updates derive the required field count from
the type byte. The initial count9 is supplied by the real preceding setup. -/
theorem type_updates_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64)
    (byteCell : source.locals.lookup (ofString "b0")=some (.val (.word byte)))
    (countCell : source.locals.lookup (ofString "nfields")=some (.val (.word 9#64)))
    (normal : evaluateHOLFiniteState source typeUpdates=(none,target)) :
    target.locals.lookup (ofString "t")=some (.val (.word byte)) ∧
      target.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount byte))) := by
  rw [type_shapes.1] at normal
  obtain ⟨typed,assignRun,countsRun⟩:=sequence_none source target _ _ normal
  have read : eval source (localVar "b0")=some (.val (.word byte)):=by simp [eval,evalHOLExact,toExact,localVar,byteCell]
  have endpoint:=assign_none source typed "t" (localVar "b0") byte read assignRun
  rw [endpoint,type_shapes.2.1] at countsRun
  obtain ⟨first,firstRun,rest⟩:=sequence_none (bind source "t" byte) target _ _ countsRun
  have firstCells:=count_step_normal (bind source "t" byte) first byte 1#64 11#64 9#64 (bind_lookup_same _ _ _)
    ((bind_lookup_other source "t" "nfields" byte (by decide)).trans countCell) firstRun
  obtain ⟨second,secondRun,restAgain⟩:=sequence_none first target _ _ rest
  have secondCells:=count_step_normal first second byte 2#64 12#64 _ firstCells.1 firstCells.2 secondRun
  obtain ⟨third,thirdRun,fourthRun⟩:=sequence_none second target _ _ restAgain
  have thirdCells:=count_step_normal second third byte 3#64 14#64 _ secondCells.1 secondCells.2 thirdRun
  exact count_step_normal third target byte 4#64 13#64 _ thirdCells.1 thirdCells.2 fourthRun

/-- The real unsigned type-byte condition selects only types1 through4. -/
theorem typed_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (byte : BitVec 64)
    (byteCell : source.locals.lookup (ofString "b0")=some (.val (.word byte))) :
    eval source typedTest=some (.val (.word (if 1≤byte.toNat ∧ byte.toNat≤4 then 1#64 else 0#64))) := by
  rw [type_shapes.2.2]
  by_cases low : byte.toNat<1 <;> by_cases high : 4<byte.toNat
  all_goals
    by_cases active : 1≤byte.toNat ∧ byte.toNat≤4
    all_goals first
      | omega
      | simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,byteCell,valueIsWord,valueWord,wordOpHOL,wordOp,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,AndOp.and,low,high,active]

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.type_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_count_bounds
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.count_step_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.type_updates_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.typed_test_read


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real normal selector supplies its actual type0..4 and required
field count, together with the SAME complete parse and caller memory frame. -/
theorem selection_tagged_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (byteCell : source.locals.lookup (ofString "b0")=some (.val (.word byte)))
    (typeZero : source.locals.lookup (ofString "t")=some (.val (.word 0#64)))
    (countNine : source.locals.lookup (ofString "nfields")=some (.val (.word 9#64)))
    (normal : evaluateHOLFiniteState source selection=(none,target)) :
    ∃ tag : BitVec 64,∃ answer,tag.toNat≤4 ∧ target.locals.lookup (ofString "t")=some (.val (.word tag)) ∧
      target.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag))) ∧
      Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer ∧
      target.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source target ∧
      ∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→target.locals.lookup key=source.locals.lookup key := by
  have observed:=typed_test_read source byte byteCell
  rw [selection_shapes.2.1,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  by_cases active : 1≤byte.toNat ∧ byte.toNat≤4
  · rw [if_pos active] at normal
    change evaluateHOLFiniteState source typedSelection=(none,target) at normal
    rw [selection_shapes.2.2.1] at normal
    obtain ⟨middle,decodeRun,updatesRun⟩:=sequence_none source target (decodeCall true) typeUpdates normal
    obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source middle pointer length true entry decodeRun
    have middleByte:=(saved (ofString "b0") (by decide)).trans byteCell
    have middleCount:=(saved (ofString "nfields") (by decide)).trans countNine
    have typedCells:=type_updates_normal middle target byte middleByte middleCount updatesRun
    have physical:=updates_readonly middle.code middle rfl
    rw [updatesRun] at physical
    have retained:=(updates_saved (ofString "top") (by decide) (by decide)).summary middle
    rw [updatesRun] at retained
    have nonzero : byte≠0#64:=by intro zero; rw [zero] at active; change 1≤0 ∧ 0≤4 at active; omega
    change Rlp.Decode.Complete (pointer+1#64) (length-1#64) answer at complete
    refine ⟨byte,answer,active.2,typedCells.1,typedCells.2,by simpa only [if_neg nonzero] using complete,
      (retained.1 rfl).trans topCell,(Rlp.CurrentItem.Frame.of_readonly physical).trans frame,?_⟩
    intro key notTop notType notCount
    have kept:=(updates_saved key notType notCount).summary middle
    rw [updatesRun] at kept
    exact (kept.1 rfl).trans (saved key notTop)
  · rw [if_neg active] at normal
    change evaluateHOLFiniteState source legacyChoice=(none,target) at normal
    rw [selection_shapes.2.2.2] at normal
    rcases conditional_none source target legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64)) normal with decodeRun|rejected
    · obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source target pointer length false entry decodeRun
      change Rlp.Decode.Complete pointer length answer at complete
      refine ⟨0#64,answer,by decide,(saved _ (by decide)).trans typeZero,?_,complete,topCell,frame,?_⟩
      · simpa [fieldCount] using (saved _ (by decide)).trans countNine
      · intro key notTop _ _
        exact saved key notTop
    · exact False.elim (raise_ne_none source (ofString "TxErr") (.const 2#64) (congrArg Prod.fst rejected))

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_tagged_normal


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem selection_entry_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap byte : BitVec 64) :
    (selectionEntry source pointer length heap byte).clock=source.clock-16 := by
  change source.clock-1-(Zero.price 400+1)=source.clock-16
  rw [Nat.sub_sub]
  rfl

/-- A genuine whole decoder return derives its actual type/count, real
complete top item and original input frame before the real field suffix.
The same observed normal setup/selector prefix spends at most60*n+29 ticks. -/
theorem setup_tagged_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ byte : BitVec 64,∃ current inner,∃ tag : BitVec 64,∃ answer,byte.toNat<256 ∧ 1≤length.toNat ∧ tag.toNat≤4 ∧ heap.toNat+400≤2952790016 ∧
      current.locals.lookup (ofString "t")=some (.val (.word tag)) ∧
      current.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag))) ∧
      Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer ∧
      current.locals.lookup (ofString "top")=some answer ∧
      PersistentNormalFrame source current heap ∧ Rlp.CurrentItem.Frame (selectionEntry source pointer length heap byte) current ∧
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=(selectionEntry source pointer length heap byte).locals.lookup key) ∧
      source.clock-current.clock≤60*length.toNat+29 ∧
      evaluateHOLFiniteState current afterSelection=(some (.returned value),inner) ∧ post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  obtain ⟨byte,inner,byteSmall,positive,room,prefixFrame,remaining,clock,physical⟩:=setup_returned source post pointer length heap entry value normal
  let selected:=selectionEntry source pointer length heap byte
  let ready:=selection_entry_ready source pointer length heap byte entry room
  let parserEntry:=selected_parser_entry source pointer length heap byte entry positive room
  have cells:=selection_entry_cells source pointer length heap byte
  rw [selection_shapes.1] at remaining
  obtain ⟨current,selectedRun,continued⟩:=sequence_returned selected inner selection afterSelection value (selection_no_return selected) remaining
  obtain ⟨tag,answer,bounded,typeCell,countCell,complete,topCell,parseFrame,saved⟩:=selection_tagged_normal selected current pointer length byte parserEntry
    cells.2.1 cells.2.2.1 cells.2.2.2.1 selectedRun
  let last:=PersistentAlloc.rounded heap 400#64
  have parserInitial:=PersistentNormalFrame.refl selected last ready.heapCell ready.heapArena ready.heapBound ready.heapAligned
  have parserPersistent:=parserInitial.after_memory selected selected current last parseFrame.metadata (by
    intro query before
    have bound : last.toNat≤2952790016:=ready.heapBound
    exact parseFrame.outside query (Or.inl (Nat.lt_of_lt_of_le before bound)))
  have guards:=PersistentAlloc.guards heap 400#64 room
  have grows : heap.toNat≤last.toNat:=by
    have covered : heap.toNat+400≤last.toNat:=guards.2.2.1
    omega
  have originalFrame:=prefixFrame.trans source selected current heap last parserPersistent grows
  have price:=selection_cost selected pointer length parserEntry
  rw [selectedRun] at price
  change selected.clock-current.clock≤60*length.toNat+13 at price
  have forward:=evaluateHOLFiniteState_clock_le selected selection
  rw [selectedRun] at forward
  change current.clock≤selected.clock at forward
  have initializedClock:=selection_entry_clock source pointer length heap byte
  change selected.clock=source.clock-16 at initializedClock
  have prefixPrice : source.clock-selected.clock≤16:=by rw [initializedClock]; omega
  have total : source.clock-current.clock≤60*length.toNat+29:=by omega
  exact ⟨byte,current,inner,tag,answer,byteSmall,positive,bounded,room,typeCell,countCell,complete,topCell,
    originalFrame,parseFrame,saved,total,continued,clock,physical⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_entry_clock
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.setup_tagged_returned


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual field suffix is priced only after this same selector has
derived its real type/count and complete parser result. -/
theorem tagged_fields_reached_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length byte : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (byteCell : source.locals.lookup (ofString "b0")=some (.val (.word byte)))
    (typeZero : source.locals.lookup (ofString "t")=some (.val (.word 0#64)))
    (countNine : source.locals.lookup (ofString "nfields")=some (.val (.word 9#64))) (tailPrice : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ tag : BitVec 64,∀ answer,
      tag.toNat≤4→current.locals.lookup (ofString "t")=some (.val (.word tag))→
      current.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag)))→
      Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer→
      current.locals.lookup (ofString "top")=some answer→Rlp.CurrentItem.Frame source current→
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=source.locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current afterSelection).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source selectionAndFields).2.clock≤60*length.toNat+13+tailPrice := by
  rw [selection_shapes.1]
  apply ClockCost.sequence_reached_current source selection afterSelection (60*length.toNat+13) tailPrice (selection_cost source pointer length entry)
  intro current normal
  obtain ⟨tag,answer,bounded,typeCell,countCell,complete,topCell,frame,saved⟩:=selection_tagged_normal source current pointer length byte entry byteCell typeZero countNine normal
  exact tail current tag answer bounded typeCell countCell complete topCell frame saved

/-- Actual setup and type selection compose on ALL outcomes. The remaining
field allowance is required only at genuinely reached parsed physical states;
no future successful field read, allocation or enclosing return is assumed. -/
theorem body_tagged_fields_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) (tailPrice : Nat)
    (tail : ∀ byte : BitVec 64,byte.toNat<256→1≤length.toNat→heap.toNat+400≤2952790016→
      ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ tag : BitVec 64,∀ answer,
      tag.toNat≤4→current.locals.lookup (ofString "t")=some (.val (.word tag))→
      current.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag)))→
      Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer→
      current.locals.lookup (ofString "top")=some answer→Rlp.CurrentItem.Frame (selectionEntry source pointer length heap byte) current→
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=(selectionEntry source pointer length heap byte).locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current afterSelection).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*length.toNat+528+tailPrice := by
  have actual:=body_reached_cost source pointer length heap entry (60*length.toNat+13+tailPrice) (by
    intro byte small positive room
    have cells:=selection_entry_cells source pointer length heap byte
    exact tagged_fields_reached_cost (selectionEntry source pointer length heap byte) pointer length byte
      (selected_parser_entry source pointer length heap byte entry positive room) cells.2.1 cells.2.2.1 cells.2.2.2.1 tailPrice
      (tail byte small positive room))
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.tagged_fields_reached_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_tagged_fields_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual parsed envelope before the type store and field-list conversion.
Its record and original input are separate; every condition is a fact about
this reached state, rather than a future accepted field or allocation. -/
structure Selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record heap tag : BitVec 64) (answer : ValueHOL 64) where
  entry : BlobHashes.Entry source pointer length heap
  nonempty : 1≤length.toNat
  recordArena : AllocatedBytes.Arena record 400
  recordAligned : record.toNat%8=0
  recordBefore : record.toNat+400≤heap.toNat
  inputBeforeRecord : pointer.toNat+length.toNat≤record.toNat
  recordCell : source.locals.lookup (ofString "tx")=some (.val (.word record))
  tagBound : tag.toNat≤4
  typeCell : source.locals.lookup (ofString "t")=some (.val (.word tag))
  fieldCountCell : source.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag)))
  topCell : source.locals.lookup (ofString "top")=some answer
  complete : Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer

/-- The actual same-return parser frame and restored caller cells construct
the complete physical field-entry model from the preceding real setup. -/
def selected_from_parser (original current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record byte tag : BitVec 64) (answer : ValueHOL 64)
    (entry : BlobHashes.Entry original pointer length record) (positive : 1≤length.toNat) (room : record.toNat+400≤2952790016)
    (bounded : tag.toNat≤4) (typeCell : current.locals.lookup (ofString "t")=some (.val (.word tag)))
    (countCell : current.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag))))
    (complete : Rlp.Decode.Complete (if tag=0#64 then pointer else pointer+1#64) (if tag=0#64 then length else length-1#64) answer)
    (topCell : current.locals.lookup (ofString "top")=some answer)
    (frame : Rlp.CurrentItem.Frame (selectionEntry original pointer length record byte) current)
    (saved : ∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=(selectionEntry original pointer length record byte).locals.lookup key) :
    Selected current pointer length record (PersistentAlloc.rounded record 400#64) tag answer := by
  let initial:=selection_entry_ready original pointer length record byte entry room
  have globals : current.globals=(selectionEntry original pointer length record byte).globals:=by
    have projected:=congrArg PanSemStateFiniteExact.globals frame.metadata
    exact projected
  have live : BlobHashes.Entry current pointer length (PersistentAlloc.rounded record 400#64):={
    initial with
    arena:=initial.arena.of_metadata frame.metadata
    pointerCell:=(saved _ (by decide) (by decide) (by decide)).trans initial.pointerCell
    lengthCell:=(saved _ (by decide) (by decide) (by decide)).trans initial.lengthCell
    heapCell:=by rw [globals]; exact initial.heapCell }
  have guards:=PersistentAlloc.guards record 400#64 room
  exact {
    entry:=live,nonempty:=positive,recordArena:=⟨entry.heapArena.lower,by omega⟩,recordAligned:=entry.heapAligned
    recordBefore:=guards.2.2.1,inputBeforeRecord:=entry.inputBefore
    recordCell:=(saved _ (by decide) (by decide) (by decide)).trans (selection_entry_cells original pointer length record byte).1
    tagBound:=bounded,typeCell:=typeCell,fieldCountCell:=countCell,topCell:=topCell,complete:=complete }

def typeStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record tag : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory record tag}

theorem Selected.store_type {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) :
    evaluateHOLFiniteState source (.store (.op .add [localVar "tx",.const 0#64]) (localVar "t"))=(none,typeStored source record tag) := by
  have addressRead : eval source (.op .add [localVar "tx",.const 0#64])=some (.val (.word record)):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.recordCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have tagRead : eval source (localVar "t")=some (.val (.word tag)):=by simp [eval,evalHOLExact,toExact,localVar,data.typeCell]
  have mapped:=AllocatedBytes.word_mapped source record 400 0 data.entry.arena.domain data.recordArena (by decide) data.recordAligned (by decide)
  exact StoreWord.execute source _ _ record tag addressRead tagRead (by simpa [byteAddress] using mapped)

def Selected.after_type {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) : Selected (typeStored source record tag) pointer length record heap tag answer :=
  {data with
    entry:={data.entry with arena:=data.entry.arena.of_metadata rfl}}

/-- The chosen typed or legacy input has the original endpoint and starts
within the original transaction, with no modular wrap at its type byte. -/
theorem Selected.input_extent {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) :
    (if tag=0#64 then pointer else pointer+1#64).toNat+(if tag=0#64 then length else length-1#64).toNat=pointer.toNat+length.toNat ∧
      (if tag=0#64 then length else length-1#64).toNat≤length.toNat ∧
      pointer.toNat≤(if tag=0#64 then pointer else pointer+1#64).toNat := by
  by_cases zero : tag=0#64
  · simp [zero]
  · simp only [if_neg zero]
    have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.inputBeforeRecord; have upper:=data.recordArena.upper; omega
    have extent:=typed_extent pointer length data.nonempty fits
    exact ⟨extent.2.2,by rw [extent.2.1]; omega,by rw [extent.1]; omega⟩

/-- The actual reached list guard supplies the exact payload arguments
and the physical converter entry, inside the original input before tx. -/
theorem Selected.payload {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer)
    (normal : evaluateHOLFiniteState source listGuard=(none,target)) :
    ∃ payloadPointer payloadLength,pointer.toNat≤payloadPointer.toNat ∧
      payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat ∧ payloadLength.toNat≤length.toNat ∧
      payloadPointer.toNat+payloadLength.toNat≤record.toNat ∧
      Nonempty (NestedLists.Entry source payloadPointer payloadLength heap) ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values payloadPointer payloadLength) := by
  let start:=if tag=0#64 then pointer else pointer+1#64
  let count:=if tag=0#64 then length else length-1#64
  have extent:=data.input_extent
  have sameEnd : start.toNat+count.toNat=pointer.toNat+length.toNat:=extent.1
  have countBound : count.toNat≤length.toNat:=extent.2.1
  have startsAfter : pointer.toNat≤start.toNat:=extent.2.2
  have fits : start.toNat+count.toNat<2^64:=by
    rw [sameEnd]
    have before:=data.inputBeforeRecord
    have upper:=data.recordArena.upper
    omega
  obtain ⟨header,payload,same,positive,number,endpoint,bounded,args⟩:=payload_of_guard source target start count answer data.complete fits data.topCell normal
  have combined : (start+header).toNat+payload.toNat=pointer.toNat+length.toNat:=endpoint.trans sameEnd
  have lower : pointer.toNat≤(start+header).toNat:=by rw [number]; omega
  have inputBefore:=data.entry.inputBefore
  have originalBefore:=data.inputBeforeRecord
  refine ⟨start+header,payload,lower,combined,Nat.le_trans bounded countBound,by rw [combined]; exact originalBefore,?_,args⟩
  exact ⟨⟨data.entry.arena,data.entry.heapCell,data.entry.heapArena,data.entry.heapBound,data.entry.heapAligned,by omega⟩⟩

/-- Physical converter output shared with the list decoders, without
requiring the caller's p/len locals to equal its top-item payload arguments. -/
def prepared_from_payload {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap count : BitVec 64} {items : List Rlp.ListItem}
    (entry : NestedLists.Entry source pointer length heap)
    (model : Rlp.ListItems target pointer length.toNat items) (countExact : count.toNat=items.length) (countBound : count.toNat≤length.toNat)
    (records : Rlp.Slices.Records target.memory heap pointer items) (room : heap.toNat+16*count.toNat≤2952790016)
    (arena : Rlp.LiveArena target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    BlobHashes.Prepared (CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)) pointer length heap (PersistentAlloc.rounded heap (count*16#64)) count items := by
  have amount : (count*16#64).toNat=16*count.toNat:=by
    rw [BitVec.toNat_mul]
    change (count.toNat*16)%2^64=16*count.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have guards:=PersistentAlloc.guards heap (count*16#64) (by rw [amount]; exact room)
  have grows : heap.toNat+16*count.toNat≤(PersistentAlloc.rounded heap (count*16#64)).toNat:=by
    have actual:=guards.2.2.1
    rw [amount] at actual
    exact actual
  let ready:=CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)
  exact {
    arena:=arena.of_frame rfl
    listCell:=by simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    itemModel:=model.transport target ready pointer length.toNat items length.isLt (by intros; rfl)
    countExact:=countExact,countBound:=countBound,records:=records
    arrayArena:=⟨entry.heapArena.lower,by omega⟩,arrayAligned:=entry.heapAligned,arrayBefore:=grows,inputBefore:=entry.inputBefore
    heapCell:=by
      change target.globals.lookup (ofString "heap_ptr")=_
      rw [globals]
      simp [HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=entry.heapArena.lower; omega,by have bound:=guards.2.2.2.1; omega⟩
    heapBound:=guards.2.2.2.1,heapAligned:=guards.2.2.2.2 }

def afterArray : ProgHOL 64:=match afterSlices with | .dec _ _ _ rest=>rest | _=>.skip
def afterArity : ProgHOL 64:=match afterArray with | .seq _ rest=>rest | _=>.skip
def fieldBody : ProgHOL 64:=match afterArity with | .dec _ _ _ (.dec _ _ _ rest)=>rest | _=>.skip
def arityGuard : ProgHOL 64:=TransactionFields.rejectUnequal (.rfield 1 (localVar "lst")) (localVar "nfields") 4#64

set_option maxRecDepth 100000 in
theorem field_setup_shapes : afterSlices=.dec (ofString "arr") .one (.rfield 0 (localVar "lst")) afterArray ∧
    afterArray=.seq arityGuard afterArity ∧
    afterArity=.dec (ofString "k") .one (.const 0#64) (.dec (ofString "w") .one (.const 0#64) fieldBody) := by
  simp (maxSteps:=1000000) only [afterArray,afterArity,fieldBody,arityGuard,TransactionFields.rejectUnequal,afterSlices,afterListGuard,
    afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selected_from_parser
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Selected.store_type
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Selected.after_type
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Selected.input_extent
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Selected.payload
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.prepared_from_payload
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_setup_shapes


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Real converted field rows before the arity check. Count is unrestricted
until the actual guard passes; the existing transaction record is before
the fresh array and the payload stays before that record. -/
structure Converted (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record array heap count tag : BitVec 64) (items : List Rlp.ListItem) where
  rows : BlobHashes.Prepared source pointer length array heap count items
  recordArena : AllocatedBytes.Arena record 400
  recordAligned : record.toNat%8=0
  recordBeforeArray : record.toNat+400≤array.toNat
  inputBeforeRecord : pointer.toNat+length.toNat≤record.toNat
  recordCell : source.locals.lookup (ofString "tx")=some (.val (.word record))
  tagBound : tag.toNat≤4
  typeCell : source.locals.lookup (ofString "t")=some (.val (.word tag))
  fieldCountCell : source.locals.lookup (ofString "nfields")=some (.val (.word (fieldCount tag)))

/-- The SAME observed converter result supplies allocated field rows while
its real caller restoration retains type/count/transaction bindings. -/
def converted_from_payload {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {rawPointer rawLength pointer length record heap count tag : BitVec 64} {answer : ValueHOL 64} {items : List Rlp.ListItem}
    (data : Selected source rawPointer rawLength record heap tag answer)
    (entry : NestedLists.Entry source pointer length heap) (before : pointer.toNat+length.toNat≤record.toNat)
    (model : Rlp.ListItems target pointer length.toNat items) (countExact : count.toNat=items.length) (countBound : count.toNat≤length.toNat)
    (records : Rlp.Slices.Records target.memory heap pointer items) (room : heap.toNat+16*count.toNat≤2952790016)
    (arena : Rlp.LiveArena target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    Converted (CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)) pointer length record heap (PersistentAlloc.rounded heap (count*16#64)) count tag items := by
  exact {
    rows:=prepared_from_payload entry model countExact countBound records room arena globals
    recordArena:=data.recordArena,recordAligned:=data.recordAligned,recordBeforeArray:=data.recordBefore,inputBeforeRecord:=before
    recordCell:=by
      simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lst"≠ofString "tx" from by decide] using data.recordCell
    tagBound:=data.tagBound
    typeCell:=by
      simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lst"≠ofString "t" from by decide] using data.typeCell
    fieldCountCell:=by
      simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lst"≠ofString "nfields" from by decide] using data.fieldCountCell }

def Converted.bound_word {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (name : String) (word : BitVec 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields") :
    Converted (bind source name word) pointer length record array heap count tag items := by
  let ready:=bind source name word
  exact {data with
    rows:={data.rows with
      arena:=data.rows.arena.of_frame rfl
      listCell:=(bind_lookup_other source name "lst" word notLst).trans data.rows.listCell
      itemModel:=data.rows.itemModel.transport source ready pointer length.toNat items length.isLt (by intros; rfl)}
    recordCell:=(bind_lookup_other source name "tx" word notTx).trans data.recordCell
    typeCell:=(bind_lookup_other source name "t" word notType).trans data.typeCell
    fieldCountCell:=(bind_lookup_other source name "nfields" word notCount).trans data.fieldCountCell }

def fieldEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) :=
  bind (bind (bind source "arr" array) "k" 0#64) "w" 0#64

def Converted.field_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) :
    Converted (fieldEntry source array) pointer length record array heap count tag items :=
  ((data.bound_word "arr" array (by decide) (by decide) (by decide) (by decide)).bound_word "k" 0#64 (by decide) (by decide) (by decide) (by decide)).bound_word "w" 0#64 (by decide) (by decide) (by decide) (by decide)

theorem field_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) :
    (fieldEntry source array).locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      (fieldEntry source array).locals.lookup (ofString "k")=some (.val (.word 0#64)) ∧
      (fieldEntry source array).locals.lookup (ofString "w")=some (.val (.word 0#64)) := by
  simp [fieldEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "w"≠ofString "arr" from by decide,show ofString "k"≠ofString "arr" from by decide,show ofString "w"≠ofString "k" from by decide]

theorem Converted.arity {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items)
    (normal : evaluateHOLFiniteState source arityGuard=(none,target)) : count=fieldCount tag := by
  apply TransactionFields.reject_unequal_normal source target (.rfield 1 (localVar "lst")) (localVar "nfields") 4#64 count (fieldCount tag) _ _ normal
  · simp [eval,evalHOLExact,toExact,localVar,data.rows.listCell,Rlp.Slices.result]
  · simp [eval,evalHOLExact,toExact,localVar,data.fieldCountCell]

/-- Actual array alias/count guard and k/w declarations. The only field
allowance required is at their real initialized state after the guard passes. -/
theorem after_slices_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (price : Nat)
    (tail : count=fieldCount tag→(fieldEntry source array).clock-(evaluateHOLFiniteState (fieldEntry source array) fieldBody).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤price := by
  rw [field_setup_shapes.1]
  have arrayRead : eval source (.rfield 0 (localVar "lst"))=some (.val (.word array)):=by
    simp [eval,evalHOLExact,toExact,localVar,data.rows.listCell,Rlp.Slices.result]
  apply ClockCost.declared_current source "arr" (.rfield 0 (localVar "lst")) array afterArray price arrayRead
  let aliased:=bind source "arr" array
  have current:=data.bound_word "arr" array (by decide) (by decide) (by decide) (by decide)
  rw [field_setup_shapes.2.1]
  unfold arityGuard TransactionFields.rejectUnequal
  have bounded:=ClockCost.stopping_guard_reached aliased (.cmp .notEqual (.rfield 1 (localVar "lst")) (localVar "nfields"))
    (.raise (ofString "TxErr") (.const 4#64)) afterArity 0 price (raise_ne_none aliased _ _) (ClockCost.raised aliased.code _ _ aliased rfl) (by
      intro passed
      have arity:=current.arity passed
      rw [field_setup_shapes.2.2]
      apply ClockCost.declared_current aliased "k" (.const 0#64) 0#64 _ price rfl
      exact ClockCost.declared_current (bind aliased "k" 0#64) "w" (.const 0#64) 0#64 fieldBody price rfl (tail arity))
  simpa only [Nat.zero_max] using bounded

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.converted_from_payload
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.bound_word
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.field_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_entry_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.arity
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.after_slices_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Remaining work at actual converted rows after their real count guard and
arr/k/w initialization. This is a cost contract, never a future normal run. -/
def ConvertedPrice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record array tag : BitVec 64) (price : Nat) : Prop :=
  ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ next count items,
    Converted current pointer length record array next count tag items→count=fieldCount tag→
    PersistentNormalFrame source current array→
    current.locals.lookup (ofString "arr")=some (.val (.word array))→
    current.locals.lookup (ofString "k")=some (.val (.word 0#64))→
    current.locals.lookup (ofString "w")=some (.val (.word 0#64))→
    current.clock-(evaluateHOLFiniteState current fieldBody).2.clock≤price

def FieldsPrice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record heap tag : BitVec 64) (price : Nat) : Prop :=
  ∀ payloadPointer payloadLength,pointer.toNat≤payloadPointer.toNat→
    payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat→payloadLength.toNat≤length.toNat→
    ConvertedPrice source payloadPointer payloadLength record heap tag price

/-- Actual scoped conversion, output allocation, alias/arity guard and
field initialization. Its same normal callee return supplies the row model
and persistent frame used to charge only the genuinely reached field body. -/
theorem payload_conversion_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {rawPointer rawLength pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source rawPointer rawLength record heap tag answer) (entry : NestedLists.Entry source pointer length heap)
    (before : pointer.toNat+length.toNat≤record.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length))
    (price : Nat) (tail : ConvertedPrice source pointer length record heap tag price) :
    source.clock-(evaluateHOLFiniteState source afterListGuard).2.clock≤71*length.toNat+price+4 := by
  have fits : pointer.toNat+length.toNat<2^64:=by have bound:=entry.heapBound; have inputBefore:=entry.inputBefore; omega
  obtain ⟨callee,called,pCell,nCell⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") Rlp.Slices.body Rlp.Slices.resultShape pointer length
    (Rlp.Slices.original_code source.code entry.arena.code)
  have bodyPrice:=Rlp.CurrentSlices.body_cost (callEntryStateHOLFinite source callee) pointer length pCell nCell (entry.arena.of_frame rfl) fits entry.arena.code
  rw [continuation_shapes.2.2]
  have actual:=ClockCost.scoped_reached_current source "lst" Rlp.Slices.resultShape (ofString "rlp_list_to_slices") sliceArguments _ Rlp.Slices.body afterSlices callee Rlp.Slices.resultShape
    (71*length.toNat+3) price args called bodyPrice (by
      intro child value normal checked
      obtain ⟨items,count,model,countExact,countBound,answerEq,records,room,arena,globals,window,metadata,above,spent⟩:=
        Rlp.CurrentSlices.body_normal (callEntryStateHOLFinite source callee) child pointer length heap pCell nCell (entry.arena.of_frame rfl)
          entry.heapCell entry.heapBound entry.inputBefore (by have bounded:=entry.heapBound; have inputBefore:=entry.inputBefore; omega) value normal
      rw [answerEq]
      let ready:=CallNormal.continuationEntry source child "lst" (Rlp.Slices.result heap count)
      have rows:=converted_from_payload data entry before model countExact countBound records room arena globals
      have frame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count entry.heapArena room metadata window
      have initialized:=frame.of_erase source child source (fieldEntry ready heap) heap rfl rfl
      have cells:=field_entry_cells ready heap
      exact after_slices_cost rows price (fun arity=>tail (fieldEntry ready heap) _ count items rows.field_entry arity initialized cells.1 cells.2.1 cells.2.2))
  omega

/-- A rejected top-kind test stops here. Only its actual passed guard
supplies the contained payload and genuine converter entry. -/
theorem after_type_store_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) (price : Nat)
    (tail : FieldsPrice source pointer length record heap tag price) :
    source.clock-(evaluateHOLFiniteState source afterTypeStore).2.clock≤71*length.toNat+price+4 := by
  rw [continuation_shapes.2.1]
  unfold listGuard TransactionFields.rejectUnequal
  have actual:=ClockCost.stopping_guard_reached source (.cmp .notEqual (.rfield 0 (localVar "top")) (.const 1#64))
    (.raise (ofString "TxErr") (.const 3#64)) afterListGuard 0 (71*length.toNat+price+4)
    (raise_ne_none source _ _) (ClockCost.raised source.code _ _ source rfl) (by
      intro passed
      obtain ⟨payloadPointer,payloadLength,lower,endpoint,bounded,before,⟨entry⟩,args⟩:=data.payload passed
      have converted:=payload_conversion_cost data entry before args price (tail payloadPointer payloadLength lower endpoint bounded)
      omega)
  simpa only [Nat.zero_max] using actual

/-- The original scalar type store is mapped inside the real400-byte
record. It changes no input bytes; the same physical model then prices all
list-kind/conversion/arity outcomes and only their actual field continuation. -/
theorem after_selection_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) (price : Nat)
    (tail : FieldsPrice (typeStored source record tag) pointer length record heap tag price) :
    source.clock-(evaluateHOLFiniteState source afterSelection).2.clock≤71*length.toNat+price+4 := by
  rw [continuation_shapes.1,evaluateHOLFiniteState_seq_line780,data.store_type]
  exact after_type_store_cost data.after_type price tail

/-- A real enclosing return reaches the actual field body with its checked
arity and initialized arr/k/w. Scope restores preserve all nonlocal effects. -/
theorem after_slices_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),post)) :
    ∃ inner,count=fieldCount tag ∧ evaluateHOLFiniteState (fieldEntry source array) fieldBody=(some (.returned value),inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rw [field_setup_shapes.1] at normal
  have read : eval source (.rfield 0 (localVar "lst"))=some (.val (.word array)):=by
    simp [eval,evalHOLExact,toExact,localVar,data.rows.listCell,Rlp.Slices.result]
  obtain ⟨aliasPost,aliasRun,aliasRestore⟩:=declaration_return_word source post "arr" (.rfield 0 (localVar "lst")) array afterArray value read normal
  let aliased:=bind source "arr" array
  have aliasedRows:=data.bound_word "arr" array (by decide) (by decide) (by decide) (by decide)
  rw [field_setup_shapes.2.1] at aliasRun
  have guarded : PureGuard arityGuard:=.ite _ (.raise _ _) .skip
  have guardRun:=guarded.normal_passed aliased aliasPost afterArity value aliasRun
  have arity:=aliasedRows.arity guardRun
  have afterGuard:=guarded.normal_continue aliased aliasPost afterArity value aliasRun
  rw [field_setup_shapes.2.2] at afterGuard
  obtain ⟨indexPost,indexRun,indexRestore⟩:=declaration_return_word aliased aliasPost "k" (.const 0#64) 0#64 (.dec (ofString "w") .one (.const 0#64) fieldBody) value rfl afterGuard
  obtain ⟨wordPost,wordRun,wordRestore⟩:=declaration_return_word (bind aliased "k" 0#64) indexPost "w" (.const 0#64) 0#64 fieldBody value rfl indexRun
  refine ⟨wordPost,arity,wordRun,?_,?_⟩
  · rw [aliasRestore,indexRestore,wordRestore]; rfl
  · rw [aliasRestore,indexRestore,wordRestore]; rfl

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.payload_conversion_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.after_type_store_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.after_selection_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.after_slices_normal


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real type store is fresh relative to the original input. Its actual
heap remains the previously allocated bounded covering heap. -/
theorem Selected.type_store_input_frame {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) : PersistentNormalFrame source (typeStored source record tag) record := by
  have initial:=PersistentNormalFrame.refl source heap data.entry.heapCell data.entry.heapArena data.entry.heapBound data.entry.heapAligned
  have earlier:=initial.lower_frontier (small:=record) (by have before:=data.recordBefore; omega)
  exact earlier.after_memory source source (typeStored source record tag) record rfl (by
    intro query before
    have other : query≠record:=by intro same; rw [same] at before; omega
    exact if_neg other)

/-- An actual returning converter/arity/initialization suffix exposes its
real field rows and same-call persistent frame at the actual field body. -/
theorem payload_conversion_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {rawPointer rawLength pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source rawPointer rawLength record heap tag answer) (entry : NestedLists.Entry source pointer length heap)
    (before : pointer.toNat+length.toNat≤record.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterListGuard=(some (.returned value),post)) :
    ∃ current next count items inner,Nonempty (Converted current pointer length record heap next count tag items) ∧ count=fieldCount tag ∧
      PersistentNormalFrame source current heap ∧
      current.locals.lookup (ofString "arr")=some (.val (.word heap)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 0#64)) ∧
      current.locals.lookup (ofString "w")=some (.val (.word 0#64)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤71*length.toNat+4 ∧
      evaluateHOLFiniteState current fieldBody=(some (.returned value),inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rw [continuation_shapes.2.2] at normal
  obtain ⟨funded,child,items,count,inner,model,countExact,countBound,records,room,arena,domain,endian,globals,window,metadata,above,forward,spent,suffixRun,restored⟩:=
    Rlp.CurrentSlices.scoped_normal source post pointer length heap entry.arena entry.heapCell entry.heapBound entry.inputBefore
      (by have bound:=entry.heapBound; have inputBefore:=entry.inputBefore; omega) "lst" sliceArguments afterSlices args value normal
  let ready:=CallNormal.continuationEntry source child "lst" (Rlp.Slices.result heap count)
  let current:=fieldEntry ready heap
  have rows:=converted_from_payload data entry before model countExact countBound records room arena globals
  obtain ⟨final,arity,fieldRun,clock,physical⟩:=after_slices_normal rows value suffixRun
  have converterFrame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count entry.heapArena room metadata window
  have currentFrame:=converterFrame.of_erase source child source current heap rfl rfl
  have cells:=field_entry_cells ready heap
  have postClock : post.clock=final.clock:=by rw [restored]; exact clock
  have postPhysical : LocalEffects.erase post=LocalEffects.erase final:=by rw [restored]; exact physical
  exact ⟨current,PersistentAlloc.rounded heap (count*16#64),count,items,final,⟨rows.field_entry⟩,arity,currentFrame,
    cells.1,cells.2.1,cells.2.2,forward,spent,fieldRun,postClock,postPhysical⟩

/-- A genuine whole after-selection return derives its input-contained field
rows, exact arity<=14, real initialized caller locals and pre-record input
frame; no future field return or successful read is supplied as a premise. -/
theorem after_selection_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record heap tag : BitVec 64} {answer : ValueHOL 64}
    (data : Selected source pointer length record heap tag answer) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSelection=(some (.returned value),post)) :
    ∃ current payloadPointer payloadLength next count items inner,
      pointer.toNat≤payloadPointer.toNat ∧ payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat ∧ payloadLength.toNat≤length.toNat ∧
      Nonempty (Converted current payloadPointer payloadLength record heap next count tag items) ∧ count=fieldCount tag ∧ count.toNat≤14 ∧
      PersistentNormalFrame source current record ∧ PersistentNormalFrame (typeStored source record tag) current heap ∧
      current.locals.lookup (ofString "arr")=some (.val (.word heap)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 0#64)) ∧ current.locals.lookup (ofString "w")=some (.val (.word 0#64)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤71*length.toNat+4 ∧
      evaluateHOLFiniteState current fieldBody=(some (.returned value),inner) ∧ post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rw [continuation_shapes.1,evaluateHOLFiniteState_seq_line780,data.store_type] at normal
  have typed:=data.after_type
  rw [continuation_shapes.2.1] at normal
  have guarded : PureGuard listGuard:=.ite _ (.raise _ _) .skip
  have passed:=guarded.normal_passed (typeStored source record tag) post afterListGuard value normal
  have remaining:=guarded.normal_continue (typeStored source record tag) post afterListGuard value normal
  obtain ⟨payloadPointer,payloadLength,lower,endpoint,bounded,before,⟨entry⟩,args⟩:=typed.payload passed
  obtain ⟨current,next,count,items,inner,rows,arity,converted,arrCell,indexCell,wordCell,forward,spent,fieldRun,clock,physical⟩:=
    payload_conversion_normal typed entry before args value remaining
  have originalFrame:=data.type_store_input_frame.trans source (typeStored source record tag) current record heap converted (by have beforeRecord:=data.recordBefore; omega)
  have countBound : count.toNat≤14:=by rw [arity]; exact (field_count_bounds tag).2
  have beforeClock : current.clock≤source.clock:=forward
  have cost : source.clock-current.clock≤71*length.toNat+4:=by
    change source.clock-current.clock≤71*payloadLength.toNat+4 at spent
    omega
  exact ⟨current,payloadPointer,payloadLength,next,count,items,inner,lower,endpoint,bounded,rows,arity,countBound,originalFrame,converted,
    arrCell,indexCell,wordCell,beforeClock,cost,fieldRun,clock,physical⟩

/-- The unchanged decoder up to genuine parsed field rows: all setup,
selector, type store, list conversion and count checks are included. Only
the actual initialized field body still needs its uniform cost allowance. -/
theorem body_rows_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record : BitVec 64)
    (entry : BlobHashes.Entry source pointer length record) (price : Nat)
    (fields : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ heap tag answer,
      Selected current pointer length record heap tag answer→FieldsPrice (typeStored current record tag) pointer length record heap tag price) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤131*length.toNat+532+price := by
  have actual:=body_tagged_fields_cost source pointer length record entry (71*length.toNat+price+4) (by
    intro byte small positive room current tag answer bounded typeCell countCell complete topCell frame saved
    let selected:=selected_from_parser source current pointer length record byte tag answer entry positive room bounded typeCell countCell complete topCell frame saved
    exact after_selection_cost selected price (fields current _ tag answer selected))
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Selected.type_store_input_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.payload_conversion_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.after_selection_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_rows_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Real initial record image: clear400 bytes, store the two raw metadata
words, then its actual selected type. Used only for the pre-field snapshot. -/
def initializedMemory (memory : WordWrites.Memory) (pointer length record tag : BitVec 64) : WordWrites.Memory :=
  StoreWord.put (StoreWord.put (StoreWord.put (Zero.finalMemory memory record 400) (record+384#64) pointer) (record+392#64) length) record tag

/-- A genuine unchanged decoder return reaches the real bounded field rows.
Its original input and exact initialized record image are retained through
the same parser, type store and converter; field execution is still actual. -/
theorem body_rows_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record : BitVec 64)
    (entry : BlobHashes.Entry source pointer length record) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current payloadPointer payloadLength array heap count tag items inner,
      pointer.toNat≤payloadPointer.toNat ∧ payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat ∧ payloadLength.toNat≤length.toNat ∧
      Nonempty (Converted current payloadPointer payloadLength record array heap count tag items) ∧ count=fieldCount tag ∧ count.toNat≤14 ∧
      PersistentNormalFrame source current record ∧
      (∀ query : BitVec 64,query.toNat<record.toNat+400→current.memory query=initializedMemory source.memory pointer length record tag query) ∧
      current.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      current.locals.lookup (ofString "k")=some (.val (.word 0#64)) ∧ current.locals.lookup (ofString "w")=some (.val (.word 0#64)) ∧
      source.clock-current.clock≤131*length.toNat+33 ∧
      evaluateHOLFiniteState current fieldBody=(some (.returned value),inner) ∧ post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  obtain ⟨byte,parsed,parsedPost,tag,answer,byteSmall,positive,bounded,room,typeCell,countCell,complete,topCell,prefixFrame,parseFrame,saved,prefixPrice,remaining,parsedClock,parsedPhysical⟩:=
    setup_tagged_returned source post pointer length record entry value normal
  let selected:=selected_from_parser source parsed pointer length record byte tag answer entry positive room bounded typeCell countCell complete topCell parseFrame saved
  obtain ⟨current,payloadPointer,payloadLength,next,count,items,inner,lower,endpoint,lengthBound,rows,arity,countBound,fieldFrame,typedFrame,arrCell,indexCell,wordCell,forward,price,fieldRun,clock,physical⟩:=
    after_selection_normal selected value remaining
  let array:=PersistentAlloc.rounded record 400#64
  have originalFrame:=prefixFrame.trans source parsed current record record fieldFrame (Nat.le_refl _)
  have finalClock : post.clock=inner.clock:=parsedClock.trans clock
  have finalPhysical : LocalEffects.erase post=LocalEffects.erase inner:=parsedPhysical.trans physical
  have totalPrice : source.clock-current.clock≤131*length.toNat+33:=by omega
  have recordFrame : ∀ query : BitVec 64,query.toNat<record.toNat+400→current.memory query=initializedMemory source.memory pointer length record tag query:=by
    intro query before
    have covered : record.toNat+400≤array.toNat:=selected.recordBefore
    have unchanged:=typedFrame.memory query (Nat.lt_of_lt_of_le before covered)
    rw [unchanged]
    change StoreWord.put parsed.memory record tag query=StoreWord.put (selectionEntry source pointer length record byte).memory record tag query
    by_cases atRecord : query=record
    · simp [StoreWord.put,atRecord]
    · simp only [StoreWord.put,if_neg atRecord]
      exact parseFrame.outside query (Or.inl (Nat.lt_of_lt_of_le before room))
  exact ⟨current,payloadPointer,payloadLength,array,next,count,tag,items,inner,lower,endpoint,lengthBound,rows,arity,countBound,originalFrame,recordFrame,
    arrCell,indexCell,wordCell,totalPrice,fieldRun,finalClock,finalPhysical⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_rows_normal


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A selected converted field supplies its actual mapped/stored row in the
real reader ABI. It does not depend on any particular caller tuple name. -/
theorem Converted.row {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (index : BitVec 64) (active : index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[index.toNat]?=some item) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : callee.lookup (ofString "i")=some (.val (.word index))) :
    TransactionNumbers.Row (callEntryStateHOLFinite source callee) array index (Rlp.Slices.itemPointer pointer items index.toNat) item.total := by
  have words:=Rlp.Slices.Records.at source.memory array pointer items data.rows.records index.toNat item selected
  have product : BitVec.ofNat 64 (16*index.toNat)=index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*index.toNat) data.rows.arena.domain data.rows.arrayArena (by omega) data.rows.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*index.toNat+8) data.rows.arena.domain data.rows.arrayArena (by omega) data.rows.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product] at firstMapped secondMapped
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.rows.inputBefore; have upper:=array.isLt; omega
  exact ⟨data.rows.arena.of_frame rfl,arrayCell,indexCell,firstMapped,by
    change source.memaddrs (array+index*16#64+8#64)
    simpa only [BitVec.add_assoc] using secondMapped,words.1,words.2,
    (data.rows.itemModel.at_span source pointer length.toNat items index.toNat item selected fits).2.2.2⟩

/-- Transport actual field provenance and array cells through observed
physical changes, retaining only the four protected caller bindings. -/
def Converted.transport {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items)
    (metadata : MemoryMetadata.erase target=MemoryMetadata.erase source)
    (listCell : target.locals.lookup (ofString "lst")=source.locals.lookup (ofString "lst"))
    (recordCell : target.locals.lookup (ofString "tx")=source.locals.lookup (ofString "tx"))
    (typeCell : target.locals.lookup (ofString "t")=source.locals.lookup (ofString "t"))
    (countCell : target.locals.lookup (ofString "nfields")=source.locals.lookup (ofString "nfields"))
    (bytes : ∀ offset : BitVec 64,offset.toNat<length.toNat→Rlp.ReadLength.byte source (pointer+offset)=Rlp.ReadLength.byte target (pointer+offset))
    (words : ∀ query : BitVec 64,array.toNat≤query.toNat→query.toNat<array.toNat+16*items.length→target.memory query=source.memory query) :
    Converted target pointer length record array heap count tag items := by
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  exact {data with
    rows:={data.rows with
      arena:=data.rows.arena.of_metadata metadata
      listCell:=listCell.trans data.rows.listCell
      itemModel:=data.rows.itemModel.transport source target pointer length.toNat items length.isLt bytes
      records:=data.rows.records.of_interval source target array pointer items (by rw [←data.rows.countExact]; have bound:=data.rows.arrayArena.upper; omega) words
      heapCell:=by rw [globals]; exact data.rows.heapCell}
    recordCell:=recordCell.trans data.recordCell,typeCell:=typeCell.trans data.typeCell,fieldCountCell:=countCell.trans data.fieldCountCell }

/-- Actual word/tuple reader returns may change scratch while retaining the
original input, converted array and protected transaction/type bindings. -/
def Converted.reader_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (name : String) (value : ValueHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (frame : Rlp.CurrentItem.Frame source target) :
    Converted (CallNormal.continuationEntry source target name value) pointer length record array heap count tag items := by
  let ready:=CallNormal.continuationEntry source target name value
  have metadata : MemoryMetadata.erase ready=MemoryMetadata.erase source:=frame.metadata
  have before : pointer.toNat+length.toNat≤2952790016:=by
    have inputBefore:=data.rows.inputBefore
    have arrayBefore:=data.rows.arrayBefore
    have bounded:=data.rows.heapBound
    omega
  have fits : pointer.toNat+length.toNat<2^64:=by omega
  have bytes:=Rlp.Slices.Window.bytes_before source ready 2952790016 2965299200 pointer length frame.outside.memory before fits
    (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
  apply data.transport metadata _ _ _ _ bytes
  all_goals first
    | simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notLst,notTx,notType,notCount]
    | skip
  intro query lower upper
  apply frame.outside query (Or.inl ?_)
  rw [←data.rows.countExact] at upper
  have arrayBefore:=data.rows.arrayBefore
  have bounded:=data.rows.heapBound
  omega

/-- A scalar or tuple record store preserves the earlier encoded payload and
later row table from its own observed finite write footprint. -/
def Converted.store_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : Converted source pointer length record array heap count tag items) (offset width : Nat) (expression : ExpHOL 64)
    (room : offset+8*width≤400)
    (valueWidth : ∀ value,eval source expression=some value→(flattenHOL value).length≤width)
    (normal : evaluateHOLFiniteState source (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)]) expression)=(none,target)) :
    Converted target pointer length record array heap count tag items := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.rows.inputBefore; have upper:=array.isLt; omega
  have addressNumber : (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset:=by
    have before:=data.recordBeforeArray
    have upper:=array.isLt
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have addressRead : eval source (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)])=some (.val (.word (record+BitVec.ofNat 64 offset))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.recordCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨same,memory⟩:=store_bounded_normal source target _ expression (record+BitVec.ofNat 64 offset) width addressRead valueWidth normal
  have metadata : MemoryMetadata.erase target=MemoryMetadata.erase source:=by rw [same]; rfl
  have window : Rlp.Slices.Window source target record.toNat (record.toNat+400):=by
    intro query outside
    apply memory query
    intro index inside equal
    have beforeArray:=data.recordBeforeArray
    have upper:=array.isLt
    have number : (record+BitVec.ofNat 64 offset+BitVec.ofNat 64 (8*index)).toNat=record.toNat+offset+8*index:=by
      rw [BitVec.toNat_add_of_lt (by rw [addressNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),addressNumber,
        BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have queryNumber:=congrArg BitVec.toNat equal
    rw [number] at queryNumber
    rcases outside with lower|higher
    all_goals omega
  have bytes:=Rlp.Slices.Window.bytes_before source target record.toNat (record.toNat+400) pointer length window data.inputBeforeRecord fits
    (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
  apply data.transport metadata _ _ _ _ bytes
  all_goals first | rw [same] | skip
  intro query lower upper
  exact window query (Or.inr (by have beforeArray:=data.recordBeforeArray; omega))

/-- Actual field-reading state, including the separate array alias and the
current mutable field index. The arity is derived by the real count guard. -/
structure FieldState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record array heap count tag index : BitVec 64) (items : List Rlp.ListItem) where
  data : Converted source pointer length record array heap count tag items
  arity : count=fieldCount tag
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  indexCell : source.locals.lookup (ofString "k")=some (.val (.word index))

theorem FieldState.count_lower {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) : 9≤count.toNat := by
  rw [data.arity]
  exact (field_count_bounds tag).1

def FieldState.reader_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (name : String) (value : ValueHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k") (frame : Rlp.CurrentItem.Frame source target) :
    FieldState (CallNormal.continuationEntry source target name value) pointer length record array heap count tag index items := {
  data:=data.data.reader_resume name value notLst notTx notType notCount frame
  arity:=data.arity
  arrayCell:=by simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notArr] using data.arrayCell
  indexCell:=by simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notK] using data.indexCell }

def FieldState.store_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (offset width : Nat) (expression : ExpHOL 64)
    (room : offset+8*width≤400)
    (valueWidth : ∀ value,eval source expression=some value→(flattenHOL value).length≤width)
    (normal : evaluateHOLFiniteState source (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)]) expression)=(none,target)) :
    FieldState target pointer length record array heap count tag index items := by
  have same:=store_none_frame source target _ expression normal
  exact ⟨data.data.store_resume offset width expression room valueWidth normal,data.arity,
    by rw [same]; exact data.arrayCell,by rw [same]; exact data.indexCell⟩

def FieldState.counter {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (next : BitVec 64) :
    FieldState (bind source "k" next) pointer length record array heap count tag next items :=
  ⟨data.data.bound_word "k" next (by decide) (by decide) (by decide) (by decide),data.arity,
    (bind_lookup_other source "k" "arr" next (by decide)).trans data.arrayCell,bind_lookup_same _ _ _⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.row
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.transport
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.reader_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.Converted.store_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.count_lower
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.reader_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.store_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.counter


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open NestedLists (Reader readerName readerBody readerShape readerCap readerOverhead)

def fieldReaderValues (reader : Reader) (array index cap error : BitVec 64) : List (ValueHOL 64):=
  [.val (.word array),.val (.word index),.val (.word cap)]++match reader with | .word=>[.val (.word error)] | _=>[]

/-- The actual scalar-word ABI has four words, including the caller's error
code (12 or14); fixed/wide readers keep their original three-word ABI. -/
theorem field_reader_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code)
    (reader : Reader) (array index cap error : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString (readerName reader)) (fieldReaderValues reader array index cap error)=some (readerBody reader,callee,readerShape reader) ∧
      callee.lookup (ofString "arr")=some (.val (.word array)) ∧ callee.lookup (ofString "i")=some (.val (.word index)) ∧
      callee.lookup (ofString (readerCap reader))=some (.val (.word cap)) := by
  cases reader with
  | fixed=>exact NestedLists.reader_environment source installed .fixed array index cap
  | wide=>exact NestedLists.reader_environment source installed .wide array index cap
  | word=>
    obtain ⟨callee,called,aCell,iCell,cCell,eCell⟩:=word_quad_environment source.code.lookup (ofString "tx_scalar_word")
      (ofString "arr") (ofString "i") (ofString "maxb") (ofString "envcode") (TransactionNumbers.body .word) .one array index cap error
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (TransactionNumbers.word_original_code source.code installed)
    exact ⟨callee,called,aCell,iCell,cCell⟩

/-- The actual index selects one real encoded field; its own byte extent is
bounded by the complete converted payload, rather than a hypothetical read. -/
theorem FieldState.select {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selectedIndex : BitVec 64) (active : selectedIndex.toNat<count.toNat) :
    ∃ item,items[selectedIndex.toNat]?=some item ∧ item.size≤length.toNat := by
  have inside : selectedIndex.toNat<items.length:=by have exactCount:=data.data.rows.countExact; omega
  let item:=items[selectedIndex.toNat]'inside
  have selected : items[selectedIndex.toNat]?=some item:=List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega
  have span:=data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected fits
  have bounded:=span.2.2.1
  rw [span.1] at bounded
  exact ⟨item,selected,bounded⟩

/-- Actual assigned fixed/numeric reader continuation, preserving the real
field index/array/type/record, and deriving its checked scalar/quad result. -/
theorem FieldState.assigned_reader_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (reader : Reader) (selectedIndex cap error : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (name : String) (arguments : List (ExpHOL 64))
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (fieldReaderValues reader array selectedIndex cap error))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) arguments)=(none,target)) :
    ∃ child value,target=CallNormal.continuationEntry source child name value ∧ FieldState target pointer length record array heap count tag index items ∧
      Rlp.CurrentItem.Frame source target ∧ shapeEqHOL (shapeOfHOLExact value) (readerShape reader)=true := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=field_reader_environment source data.data.rows.arena.code reader array selectedIndex cap error
  obtain ⟨funded,values,body,actual,shape,child,value,argsRead,lookup,bodyRun,checked,endpoint⟩:=CallNormal.local_data source target (ofString name) _ arguments normal
  have valueEq:=Option.some.inj (argsRead.symm.trans args)
  subst values
  have same:=Option.some.inj (lookup.symm.trans called)
  have bodyEq:=congrArg Prod.fst same
  have actualEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change body=readerBody reader at bodyEq
  change actual=callee at actualEq
  change shape=readerShape reader at shapeEq
  subst body actual shape
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have frame:=NestedLists.reader_body_frame reader row cCell value bodyRun
  have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
  refine ⟨child,value,endpoint,?_,?_,checked⟩
  · rw [endpoint]
    exact data.reader_resume name value notLst notTx notType notCount notArr notK callerFrame
  · exact callerFrame.of_erase rfl (by rw [endpoint]; rfl)

/-- Every actual reader outcome is charged. Its following work is required
only after this SAME assigned call normally returned and retained the real
row state and return shape; no future result or funding is an entry premise. -/
theorem FieldState.assigned_reader_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (reader : Reader) (selectedIndex cap error : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (price : Nat)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (fieldReaderValues reader array selectedIndex cap error))
    (tail : ∀ child value,let ready:=CallNormal.continuationEntry source child name value
      FieldState ready pointer length record array heap count tag index items→Rlp.CurrentItem.Frame source ready→
      shapeEqHOL (shapeOfHOLExact value) (readerShape reader)=true→ ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.seq (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) arguments) continuation)).2.clock≤
      60*item.size+readerOverhead reader+price := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=field_reader_environment source data.data.rows.arena.code reader array selectedIndex cap error
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have bodyPrice:=NestedLists.reader_body_cost reader row cCell
  have callerPrice:=ClockCost.assigned_current source (some (.local,ofString name)) _ arguments _ (readerBody reader) callee (readerShape reader)
    (60*item.total.toNat+readerOverhead reader-1) args called bodyPrice
  have actual:=ClockCost.sequence_reached_current source _ continuation ((60*item.total.toNat+readerOverhead reader-1)+1) price callerPrice (by
    intro target normal
    obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_reader_normal reader selectedIndex cap error active item selected name arguments
      notLst notTx notType notCount notArr notK args normal
    rw [endpoint] at next frame ⊢
    exact tail child value next frame checked)
  have size:=(data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected (by
    have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega)).1
  rw [size] at actual
  cases reader <;> simp only [readerOverhead] at actual ⊢ <;> omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_reader_environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.select
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.assigned_reader_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.assigned_reader_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open NestedLists (Reader readerName readerBody readerShape readerCap readerOverhead)

def chainProgram : ProgHOL 64:=match fieldBody with | .seq first _=>first | _=>.skip
def afterChain : ProgHOL 64:=match fieldBody with | .seq _ rest=>rest | _=>.skip
def afterVector : ProgHOL 64:=match afterChain with | .dec _ _ _ rest=>rest | _=>.skip
def chainArguments : List (ExpHOL 64):=[localVar "arr",.const 0#64,.const 8#64,.const 12#64]
def chainCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") chainArguments
def chainStore : ProgHOL 64:=.store (.op .add [localVar "tx",.const 8#64]) (localVar "w")
def chainAfterRead : ProgHOL 64:=.seq chainStore (.assign .local (ofString "k") (.const 1#64))

set_option maxRecDepth 100000 in
theorem chain_shapes : fieldBody=.seq chainProgram afterChain ∧
    afterChain=.dec (ofString "v") RlpWrite.U256Value.tupleShape zeroTop afterVector ∧
    chainProgram=.ite (.cmp .notEqual (localVar "t") (.const 0#64)) (.seq chainCall chainAfterRead) .skip := by
  simp (maxSteps:=1000000) only [chainProgram,afterChain,afterVector,chainCall,chainAfterRead,chainStore,chainArguments,fieldBody,
    afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,zeroTop,RlpWrite.U256Value.tupleShape,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.chain_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) chainArguments=some (fieldReaderValues .word array 0#64 8#64 12#64) := by
  simp [chainArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell]

theorem FieldState.chain_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) :
    source.clock-(evaluateHOLFiniteState source chainProgram).2.clock≤60*length.toNat+21 := by
  have active : (0#64 : BitVec 64).toNat<count.toNat:=by have lower:=data.count_lower; change 0<count.toNat; omega
  obtain ⟨item,selected,bounded⟩:=data.select 0#64 active
  have branch:=data.assigned_reader_cost .word 0#64 8#64 12#64 active item selected "w" chainArguments chainAfterRead 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.chain_arguments (by
      intro child value
      dsimp only
      intro next frame checked
      exact ClockCost.sequence _ chainStore (.assign .local (ofString "k") (.const 1#64)) 0 0
        (ClockCost.store _ _ _) (ClockCost.assign _ _ _) _ rfl)
  have branchPrice : source.clock-(evaluateHOLFiniteState source (.seq chainCall chainAfterRead)).2.clock≤60*length.toNat+21:=by
    change source.clock-(evaluateHOLFiniteState source (.seq chainCall chainAfterRead)).2.clock≤60*item.size+21+0 at branch
    omega
  rw [chain_shapes.2.2]
  simpa only [Nat.max_zero] using ClockCost.conditional_current source (.cmp .notEqual (localVar "t") (.const 0#64))
    (.seq chainCall chainAfterRead) .skip (60*length.toNat+21) 0 branchPrice (ClockCost.skip source.code source rfl)

/-- The actual typed branch sets k1 after its same observed chain-ID read
and record write; the real legacy branch leaves k0. -/
theorem FieldState.chain_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items)
    (normal : evaluateHOLFiniteState source chainProgram=(none,target)) :
    Nonempty (FieldState target pointer length record array heap count tag (if tag=0#64 then 0#64 else 1#64) items) := by
  have observed : eval source (.cmp .notEqual (localVar "t") (.const 0#64))=some (.val (.word (if tag=0#64 then 0#64 else 1#64))):=by
    by_cases zero : tag=0#64
    all_goals simp [eval,evalHOLExact,toExact,localVar,data.data.typeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  rw [chain_shapes.2.2,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  by_cases zero : tag=0#64
  · rw [if_pos zero] at normal
    change evaluateHOLFiniteState source .skip=(none,target) at normal
    rw [evaluateHOLFiniteState_skip] at normal
    have endpoint : source=target:=congrArg Prod.snd normal
    rw [←endpoint,if_pos zero]
    exact ⟨data⟩
  · rw [if_neg zero] at normal
    change evaluateHOLFiniteState source (.seq chainCall chainAfterRead)=(none,target) at normal
    obtain ⟨readerPost,readRun,rest⟩:=sequence_none source target chainCall chainAfterRead normal
    have active : (0#64 : BitVec 64).toNat<count.toNat:=by have lower:=data.count_lower; change 0<count.toNat; omega
    obtain ⟨item,selected,bounded⟩:=data.select 0#64 active
    obtain ⟨child,value,readerEq,next,frame,checked⟩:=data.assigned_reader_normal .word 0#64 8#64 12#64 active item selected "w" chainArguments
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.chain_arguments readRun
    have cell : readerPost.locals.lookup (ofString "w")=some value:=by
      rw [readerEq]
      simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have valueRead : eval readerPost (localVar "w")=some value:=by simp [eval,evalHOLExact,toExact,localVar,cell]
    have width : ∀ actual,eval readerPost (localVar "w")=some actual→(flattenHOL actual).length≤1:=by
      intro actual actualRead
      have same:=Option.some.inj (actualRead.symm.trans valueRead)
      rw [same]
      exact Nat.le_of_eq (AuthorizationFields.value_width .word value checked)
    obtain ⟨stored,storeRun,incrementRun⟩:=sequence_none readerPost target chainStore (.assign .local (ofString "k") (.const 1#64)) rest
    have storedData:=next.store_resume 8 1 (localVar "w") (by decide) width storeRun
    have endpoint:=assign_none stored target "k" (.const 1#64) 1#64 rfl incrementRun
    rw [endpoint,if_neg zero]
    exact ⟨storedData.counter 1#64⟩

/-- Real field prefix through the chain-ID branch, retaining its actual
next index for the remaining source program on every continuing path. -/
theorem field_chain_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (if tag=0#64 then 0#64 else 1#64) items→
      current.clock-(evaluateHOLFiniteState current afterChain).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source fieldBody).2.clock≤60*length.toNat+21+price := by
  rw [chain_shapes.1]
  apply ClockCost.sequence_reached_current source chainProgram afterChain (60*length.toNat+21) price data.chain_cost
  intro current normal
  obtain ⟨next⟩:=data.chain_normal normal
  exact tail current next

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.chain_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.chain_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.chain_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.chain_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_chain_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open NestedLists (Reader readerName readerBody readerShape readerCap readerOverhead)

def FieldState.local_value {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (name : String) (value : ValueHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k") :
    FieldState (setVarHOLFinite (ofString name) value source) pointer length record array heap count tag index items :=
  data.reader_resume (target:=source) name value notLst notTx notType notCount notArr notK (Rlp.CurrentItem.Frame.of_readonly rfl)

/-- Real vector declaration preserves the physical row state and index;
failed expression/shape outcomes also spend no source ticks. -/
theorem vector_setup_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag index items→
      current.clock-(evaluateHOLFiniteState current afterVector).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterChain).2.clock≤price := by
  rw [chain_shapes.2.1]
  apply ClockCost.declared_reached_current source (ofString "v") RlpWrite.U256Value.tupleShape zeroTop afterVector price
  intro value read checked
  have same : value=.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]:=Option.some.inj (read.symm.trans rfl)
  subst value
  exact tail _ (data.local_value "v" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

/-- A standalone actual assigned reader, including every stopped outcome. -/
theorem FieldState.reader_call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (reader : Reader) (selectedIndex cap error : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (name : String) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (fieldReaderValues reader array selectedIndex cap error)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) arguments)).2.clock≤60*item.size+readerOverhead reader := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=field_reader_environment source data.data.rows.arena.code reader array selectedIndex cap error
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have actual:=ClockCost.assigned_current source (some (.local,ofString name)) _ arguments _ (readerBody reader) callee (readerShape reader)
    (60*item.total.toNat+readerOverhead reader-1) args called (NestedLists.reader_body_cost reader row cCell)
  have span:=data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected (by
    have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega)
  rw [span.1] at actual
  cases reader <;> simp only [readerOverhead] at actual ⊢ <;> omega

def nonceChoice : ProgHOL 64:=match afterVector with | .seq first _=>first | _=>.skip
def nonceSuffix : ProgHOL 64:=match afterVector with | .seq _ rest=>rest | _=>.skip
def afterNonce : ProgHOL 64:=match nonceSuffix with | .seq _ (.seq _ rest)=>rest | _=>.skip
def nonceWordArguments : List (ExpHOL 64):=[localVar "arr",localVar "k",.const 8#64,.const 12#64]
def nonceWideArguments : List (ExpHOL 64):=[localVar "arr",localVar "k",.const 32#64]
def nonceWordCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") nonceWordArguments
def nonceWideCall : ProgHOL 64:=.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") nonceWideArguments
def noncePack : ExpHOL 64:=.rstruct [localVar "w",.const 0#64,.const 0#64,.const 0#64]
def nonceWordProgram : ProgHOL 64:=.seq nonceWordCall (.assign .local (ofString "v") noncePack)
def nonceStore : ProgHOL 64:=.store (.op .add [localVar "tx",.const 16#64]) (localVar "v")
def nonceIncrement : ProgHOL 64:=.assign .local (ofString "k") (.op .add [localVar "k",.const 1#64])

set_option maxRecDepth 100000 in
theorem nonce_shapes : afterVector=.seq nonceChoice nonceSuffix ∧
    nonceChoice=.ite (.cmp .equal (localVar "t") (.const 4#64)) nonceWordProgram nonceWideCall ∧
    nonceSuffix=.seq nonceStore (.seq nonceIncrement afterNonce) := by
  simp (maxSteps:=1000000) only [nonceChoice,nonceSuffix,afterNonce,nonceWordProgram,nonceWordCall,nonceWideCall,nonceStore,nonceIncrement,noncePack,
    nonceWordArguments,nonceWideArguments,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.nonce_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) nonceWordArguments=some (fieldReaderValues .word array index 8#64 12#64) ∧
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) nonceWideArguments=some (fieldReaderValues .wide array index 32#64 0#64) := by
  simp [nonceWordArguments,nonceWideArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell]

theorem FieldState.nonce_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤1) :
    source.clock-(evaluateHOLFiniteState source nonceChoice).2.clock≤60*length.toNat+46 := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have wordPrice:=data.assigned_reader_cost .word index 8#64 12#64 active item selected "w" nonceWordArguments (.assign .local (ofString "v") noncePack) 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.nonce_arguments.1 (by
      intro child value
      dsimp only
      intro next frame checked
      exact ClockCost.assign _ _ _ _ rfl)
  have widePrice:=data.reader_call_cost .wide index 32#64 0#64 active item selected "v" nonceWideArguments data.nonce_arguments.2
  have word : source.clock-(evaluateHOLFiniteState source nonceWordProgram).2.clock≤60*length.toNat+46:=by
    change source.clock-(evaluateHOLFiniteState source nonceWordProgram).2.clock≤60*item.size+21+0 at wordPrice
    omega
  have wide : source.clock-(evaluateHOLFiniteState source nonceWideCall).2.clock≤60*length.toNat+46:=by
    change source.clock-(evaluateHOLFiniteState source nonceWideCall).2.clock≤60*item.size+46 at widePrice
    omega
  rw [nonce_shapes.2.1]
  simpa only [Nat.max_self] using ClockCost.conditional_current source (.cmp .equal (localVar "t") (.const 4#64)) nonceWordProgram nonceWideCall
    (60*length.toNat+46) (60*length.toNat+46) word wide

/-- Actual local assignment, including tuple values, determines the complete
local update on its observed normal path. -/
theorem local_assignment_none {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (expression : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source expression=some value)
    (normal : evaluateHOLFiniteState source (.assign .local (ofString name) expression)=(none,target)) :
    target=setVarHOLFinite (ofString name) value source := by
  simp only [eval] at read
  rw [evaluateHOLFiniteState_assign,read] at normal
  simp only at normal
  split at normal
  · exact (congrArg Prod.snd normal).symm
  · cases normal

/-- Both real nonce paths produce the SAME checked four-word v, preserving
all field geometry/index. Type4's scalar is packed only after its actual
normal word result; the other path uses the actual wide-reader result. -/
theorem FieldState.nonce_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤1)
    (normal : evaluateHOLFiniteState source nonceChoice=(none,target)) :
    ∃ value,Nonempty (FieldState target pointer length record array heap count tag index items) ∧
      target.locals.lookup (ofString "v")=some value ∧ shapeEqHOL (shapeOfHOLExact value) RlpWrite.U256Value.tupleShape=true := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  rw [nonce_shapes.2.1] at normal
  rcases conditional_none source target (.cmp .equal (localVar "t") (.const 4#64)) nonceWordProgram nonceWideCall normal with wordRun|wideRun
  · obtain ⟨readerPost,readRun,packRun⟩:=sequence_none source target nonceWordCall (.assign .local (ofString "v") noncePack) wordRun
    obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_reader_normal .word index 8#64 12#64 active item selected "w" nonceWordArguments
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.nonce_arguments.1 readRun
    obtain ⟨word,valueEq⟩:=RlpWrite.U256Value.scalar_word value ((shapeEqHOL_eq_true _ _).mp checked)
    have cell : readerPost.locals.lookup (ofString "w")=some (.val (.word word)):=by
      rw [endpoint,valueEq]
      simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    let packed : ValueHOL 64:=.rStruct [.val (.word word),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
    have read : eval readerPost noncePack=some packed:=by
      simp [noncePack,packed,eval,evalHOLExact,evalListHOLExact,toExact,localVar,cell]
    have packedEq:=local_assignment_none readerPost target "v" noncePack packed read packRun
    rw [packedEq]
    exact ⟨packed,⟨next.local_value "v" packed (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
      by simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE],by simp [packed,shapeOfHOLExact,RlpWrite.U256Value.tupleShape,shapeEqHOL_eq_true]⟩
  · obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_reader_normal .wide index 32#64 0#64 active item selected "v" nonceWideArguments
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.nonce_arguments.2 wideRun
    refine ⟨value,⟨next⟩,?_,checked⟩
    rw [endpoint]
    simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem nonce_suffix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (value : ValueHOL 64)
    (cell : source.locals.lookup (ofString "v")=some value) (checked : shapeEqHOL (shapeOfHOLExact value) RlpWrite.U256Value.tupleShape=true) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterNonce).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source nonceSuffix).2.clock≤price := by
  have read : eval source (localVar "v")=some value:=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have width : ∀ actual,eval source (localVar "v")=some actual→(flattenHOL actual).length≤4:=by
    intro actual actualRead
    have same:=Option.some.inj (actualRead.symm.trans read)
    rw [same]
    exact Nat.le_of_eq (AuthorizationFields.value_width .wide value checked)
  rw [nonce_shapes.2.2]
  have actual:=ClockCost.sequence_reached_current source nonceStore (.seq nonceIncrement afterNonce) 0 price (ClockCost.store source.code _ _ source rfl) (by
    intro stored storeRun
    have storedData:=data.store_resume 16 4 (localVar "v") (by decide) width storeRun
    have rest:=ClockCost.sequence_reached_current stored nonceIncrement afterNonce 0 price (ClockCost.assign stored.code _ _ stored rfl) (by
      intro current incrementRun
      have nextRead : eval stored (.op .add [localVar "k",.const 1#64])=some (.val (.word (index+1#64))):=by
        simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,storedData.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
      have endpoint:=assign_none stored current "k" _ _ nextRead incrementRun
      rw [endpoint]
      exact tail _ (storedData.counter (index+1#64)))
    simpa only [Nat.zero_add] using rest)
  simpa only [Nat.zero_add] using actual

theorem nonce_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤1) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterNonce).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterVector).2.clock≤60*length.toNat+46+price := by
  rw [nonce_shapes.1]
  apply ClockCost.sequence_reached_current source nonceChoice nonceSuffix (60*length.toNat+46) price (data.nonce_choice_cost small)
  intro current normal
  obtain ⟨value,⟨next⟩,cell,checked⟩:=data.nonce_choice_normal small normal
  exact nonce_suffix_cost next value cell checked price tail

/-- Actual chain-ID/vector/nonce prefix of the unchanged field decoder,
retaining the genuine next index for fee decoding and every stopped path. -/
theorem chain_nonce_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag ((if tag=0#64 then 0#64 else 1#64)+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterNonce).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source fieldBody).2.clock≤120*length.toNat+67+price := by
  have actual:=field_chain_cost data (60*length.toNat+46+price) (by
    intro current next
    apply vector_setup_cost next (60*length.toNat+46+price)
    intro declared prepared
    exact nonce_prefix_cost prepared (by split_ifs <;> decide) price tail)
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.local_value
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.vector_setup_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.reader_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonce_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.nonce_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.nonce_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.local_assignment_none
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.nonce_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonce_suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonce_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.chain_nonce_prefix_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open NestedLists (Reader readerName readerBody readerShape readerCap readerOverhead)

/-- Original read/store pairs use the SAME observed reader value. The actual
normal store derives its finite footprint and leaves the input/table/index
ready for following work; early read/store failures stay covered. -/
theorem FieldState.read_store_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (reader : Reader) (selectedIndex cap error : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (name : String) (arguments : List (ExpHOL 64)) (offset : Nat) (room : offset+8*AuthorizationFields.width reader≤400)
    (continuation : ProgHOL 64) (price : Nat)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (fieldReaderValues reader array selectedIndex cap error))
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag index items→
      current.clock-(evaluateHOLFiniteState current continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.seq (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) arguments)
      (.seq (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)]) (localVar name)) continuation))).2.clock≤60*item.size+readerOverhead reader+price := by
  apply data.assigned_reader_cost reader selectedIndex cap error active item selected name arguments _ price notLst notTx notType notCount notArr notK args
  intro child value
  dsimp only
  intro next frame checked
  let ready:=CallNormal.continuationEntry source child name value
  have cell : ready.locals.lookup (ofString name)=some value:=by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have read : eval ready (localVar name)=some value:=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have width : ∀ actual,eval ready (localVar name)=some actual→(flattenHOL actual).length≤AuthorizationFields.width reader:=by
    intro actual actualRead
    have same:=Option.some.inj (actualRead.symm.trans read)
    rw [same]
    exact Nat.le_of_eq (AuthorizationFields.value_width reader value checked)
  have actual:=ClockCost.sequence_reached_current ready _ continuation 0 price (ClockCost.store ready.code _ _ ready rfl) (by
    intro current normal
    exact tail current (next.store_resume offset (AuthorizationFields.width reader) (localVar name) room width normal))
  simpa only [Nat.zero_add] using actual

/-- Actual mutable field-index advance, without assuming any following read
succeeds. Word wrapping is retained; later row bounds use its real value. -/
theorem FieldState.advance_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (amount : BitVec 64) (continuation : ProgHOL 64) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag (index+amount) items→
      current.clock-(evaluateHOLFiniteState current continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.seq (.assign .local (ofString "k") (.op .add [localVar "k",.const amount])) continuation)).2.clock≤price := by
  have actual:=ClockCost.sequence_reached_current source _ continuation 0 price (ClockCost.assign source.code _ _ source rfl) (by
    intro current normal
    have read : eval source (.op .add [localVar "k",.const amount])=some (.val (.word (index+amount))):=by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have endpoint:=assign_none source current "k" _ _ read normal
    rw [endpoint]
    exact tail _ (data.counter (index+amount)))
  simpa only [Nat.zero_add] using actual

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.read_store_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.advance_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open NestedLists (Reader readerName readerBody readerShape readerCap readerOverhead)

/-- Invert the same observed read/store pair, leaving its actual continuing
state available for an index update or another real field read. -/
theorem FieldState.read_store_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (reader : Reader) (selectedIndex cap error : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (name : String) (arguments : List (ExpHOL 64)) (offset : Nat) (room : offset+8*AuthorizationFields.width reader≤400)
    (continuation : ProgHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (fieldReaderValues reader array selectedIndex cap error))
    (normal : evaluateHOLFiniteState source (.seq (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) arguments)
      (.seq (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)]) (localVar name)) continuation))=(none,target)) :
    ∃ current,Nonempty (FieldState current pointer length record array heap count tag index items) ∧ evaluateHOLFiniteState current continuation=(none,target) := by
  obtain ⟨returned,readRun,rest⟩:=sequence_none source target _ _ normal
  obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_reader_normal reader selectedIndex cap error active item selected name arguments
    notLst notTx notType notCount notArr notK args readRun
  have cell : returned.locals.lookup (ofString name)=some value:=by
    rw [endpoint]
    simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have read : eval returned (localVar name)=some value:=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have width : ∀ actual,eval returned (localVar name)=some actual→(flattenHOL actual).length≤AuthorizationFields.width reader:=by
    intro actual actualRead
    have same:=Option.some.inj (actualRead.symm.trans read)
    rw [same]
    exact Nat.le_of_eq (AuthorizationFields.value_width reader value checked)
  obtain ⟨current,storeRun,continued⟩:=sequence_none returned target _ continuation rest
  exact ⟨current,⟨next.store_resume offset (AuthorizationFields.width reader) (localVar name) room width storeRun⟩,continued⟩

theorem FieldState.advance_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (amount : BitVec 64)
    (normal : evaluateHOLFiniteState source (.assign .local (ofString "k") (.op .add [localVar "k",.const amount]))=(none,target)) :
    Nonempty (FieldState target pointer length record array heap count tag (index+amount) items) := by
  have read : eval source (.op .add [localVar "k",.const amount])=some (.val (.word (index+amount))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have endpoint:=assign_none source target "k" _ _ read normal
  rw [endpoint]
  exact ⟨data.counter (index+amount)⟩

def feeChoice : ProgHOL 64:=match afterNonce with | .seq first _=>first | _=>.skip
def afterFees : ProgHOL 64:=match afterNonce with | .seq _ rest=>rest | _=>.skip
def feeTest : ExpHOL 64:=.cmp .notLower (.const 1#64) (localVar "t")
def feeArguments (second : Bool) : List (ExpHOL 64):=
  [localVar "arr",if second then .op .add [localVar "k",.const 1#64] else localVar "k",.const 0#64]
def feeCall (second : Bool) : ProgHOL 64:=.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") (feeArguments second)
def fieldStore (offset : Nat) (name : String) : ProgHOL 64:=.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 offset)]) (localVar name)
def indexAdvance (amount : BitVec 64) : ProgHOL 64:=.assign .local (ofString "k") (.op .add [localVar "k",.const amount])
def feeOne : ProgHOL 64:=.seq (feeCall false) (.seq (fieldStore 48 "v") (indexAdvance 1#64))
def feeSecond : ProgHOL 64:=.seq (feeCall true) (.seq (fieldStore 112 "v") (indexAdvance 2#64))
def feeTwo : ProgHOL 64:=.seq (feeCall false) (.seq (fieldStore 80 "v") feeSecond)

set_option maxRecDepth 100000 in
theorem fee_shapes : afterNonce=.seq feeChoice afterFees ∧ feeChoice=.ite feeTest feeOne feeTwo := by
  simp (maxSteps:=1000000) only [feeChoice,afterFees,feeTest,feeOne,feeTwo,feeSecond,feeCall,feeArguments,fieldStore,indexAdvance,
    afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.fee_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (second : Bool) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (feeArguments second)=
      some (fieldReaderValues .wide array (if second then index+1#64 else index) 0#64 0#64) := by
  cases second <;> simp [feeArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell,
    valueIsWord,valueWord,wordOpHOL,wordOp]

theorem FieldState.fee_second_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤2) :
    source.clock-(evaluateHOLFiniteState source feeSecond).2.clock≤60*length.toNat+46 := by
  have nextNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have active : (index+1#64).toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select (index+1#64) active
  have actual:=data.read_store_cost .wide (index+1#64) 0#64 0#64 active item selected "v" (feeArguments true) 112 (by decide)
    (indexAdvance 2#64) 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.fee_arguments true)
    (by intro current next; exact ClockCost.assign _ _ _ _ rfl)
  change source.clock-(evaluateHOLFiniteState source feeSecond).2.clock≤60*item.size+46+0 at actual
  omega

theorem FieldState.fee_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤2) :
    source.clock-(evaluateHOLFiniteState source feeChoice).2.clock≤120*length.toNat+92 := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have first:=data.read_store_cost .wide index 0#64 0#64 active item selected "v" (feeArguments false) 48 (by decide)
    (indexAdvance 1#64) 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.fee_arguments false)
    (by intro current next; exact ClockCost.assign _ _ _ _ rfl)
  have second:=data.read_store_cost .wide index 0#64 0#64 active item selected "v" (feeArguments false) 80 (by decide)
    feeSecond (60*length.toNat+46) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.fee_arguments false)
    (by intro current next; exact next.fee_second_cost small)
  have one : source.clock-(evaluateHOLFiniteState source feeOne).2.clock≤120*length.toNat+92:=by
    change source.clock-(evaluateHOLFiniteState source feeOne).2.clock≤60*item.size+46+0 at first
    omega
  have two : source.clock-(evaluateHOLFiniteState source feeTwo).2.clock≤120*length.toNat+92:=by
    change source.clock-(evaluateHOLFiniteState source feeTwo).2.clock≤60*item.size+46+(60*length.toNat+46) at second
    omega
  rw [fee_shapes.2]
  simpa only [Nat.max_self] using ClockCost.conditional_current source feeTest feeOne feeTwo _ _ one two

/-- Actual branch selection determines the real counter increase, rather
than assuming which fee layout a later reader will use. -/
theorem FieldState.fee_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤2)
    (normal : evaluateHOLFiniteState source feeChoice=(none,target)) :
    Nonempty (FieldState target pointer length record array heap count tag (index+(if tag.toNat≤1 then 1#64 else 2#64)) items) := by
  have observed : eval source feeTest=some (.val (.word (if tag.toNat≤1 then 1#64 else 0#64))):=by
    by_cases low : tag.toNat≤1
    all_goals simp [feeTest,eval,evalHOLExact,toExact,localVar,data.data.typeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,low]
  rw [fee_shapes.2,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  by_cases low : tag.toNat≤1
  · rw [if_pos low] at normal
    change evaluateHOLFiniteState source feeOne=(none,target) at normal
    obtain ⟨stored,⟨next⟩,advanceRun⟩:=data.read_store_normal .wide index 0#64 0#64 active item selected "v" (feeArguments false) 48 (by decide)
      (indexAdvance 1#64) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.fee_arguments false) normal
    rw [if_pos low]
    exact next.advance_normal 1#64 advanceRun
  · rw [if_neg low] at normal
    change evaluateHOLFiniteState source feeTwo=(none,target) at normal
    obtain ⟨firstStored,⟨next⟩,secondRun⟩:=data.read_store_normal .wide index 0#64 0#64 active item selected "v" (feeArguments false) 80 (by decide)
      feeSecond (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.fee_arguments false) normal
    have nextNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
    have secondActive : (index+1#64).toNat<count.toNat:=by have lower:=data.count_lower; omega
    obtain ⟨secondItem,secondSelected,secondBounded⟩:=next.select (index+1#64) secondActive
    obtain ⟨secondStored,⟨last⟩,advanceRun⟩:=next.read_store_normal .wide (index+1#64) 0#64 0#64 secondActive secondItem secondSelected "v" (feeArguments true) 112 (by decide)
      (indexAdvance 2#64) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (next.fee_arguments true) secondRun
    rw [if_neg low]
    exact last.advance_normal 2#64 advanceRun

theorem fee_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤2) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (index+(if tag.toNat≤1 then 1#64 else 2#64)) items→
      current.clock-(evaluateHOLFiniteState current afterFees).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterNonce).2.clock≤120*length.toNat+92+price := by
  rw [fee_shapes.1]
  apply ClockCost.sequence_reached_current source feeChoice afterFees _ price (data.fee_choice_cost small)
  intro current normal
  obtain ⟨next⟩:=data.fee_choice_normal small normal
  exact tail current next

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.read_store_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.advance_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fee_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.fee_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.fee_second_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.fee_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.fee_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fee_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def gasArguments : List (ExpHOL 64):=[localVar "arr",localVar "k",.const 0#64,.const 14#64]
def gasCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "tx_scalar_word") gasArguments
def afterGas : ProgHOL 64:=match afterFees with | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem gas_shape : afterFees=.seq gasCall (.seq (fieldStore 144 "w") (.seq (indexAdvance 1#64) afterGas)) := by
  simp (maxSteps:=1000000) only [gasCall,gasArguments,afterGas,afterFees,fieldStore,indexAdvance,afterNonce,nonceSuffix,afterVector,afterChain,
    fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

theorem FieldState.gas_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) gasArguments=some (fieldReaderValues .word array index 0#64 14#64) := by
  simp [gasArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell]

/-- The original gas reader uses its own error code14; its genuine checked
word is stored before the real index advance and destination continuation. -/
theorem gas_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤4) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterGas).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterFees).2.clock≤60*length.toNat+21+price := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  rw [gas_shape]
  have actual:=data.read_store_cost .word index 0#64 14#64 active item selected "w" gasArguments 144 (by decide)
    (.seq (indexAdvance 1#64) afterGas) price (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.gas_arguments (by
      intro current next
      exact next.advance_cost 1#64 afterGas price tail)
  change source.clock-(evaluateHOLFiniteState source (.seq gasCall (.seq (fieldStore 144 "w") (.seq (indexAdvance 1#64) afterGas)))).2.clock≤60*item.size+21+price at actual
  omega

def nonceIndex (tag : BitVec 64) : BitVec 64:=(if tag=0#64 then 0#64 else 1#64)+1#64
def feeIndex (tag : BitVec 64) : BitVec 64:=nonceIndex tag+(if tag.toNat≤1 then 1#64 else 2#64)
def gasIndex (tag : BitVec 64) : BitVec 64:=feeIndex tag+1#64

theorem nonce_index_bound (tag : BitVec 64) : (nonceIndex tag).toNat≤2 := by
  unfold nonceIndex
  split_ifs <;> decide

theorem fee_index_bound (tag : BitVec 64) : (feeIndex tag).toNat≤4 := by
  have small:=nonce_index_bound tag
  unfold feeIndex
  split_ifs
  all_goals rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; simp only [BitVec.toNat_ofNat]; omega

theorem gas_index_bound (tag : BitVec 64) : (gasIndex tag).toNat≤5 := by
  have small:=fee_index_bound tag
  unfold gasIndex
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The actual field prefix through gas, retaining the type-dependent field
index used by its remaining destination/value/data/list/signature work. -/
theorem fields_through_gas_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (gasIndex tag) items→
      current.clock-(evaluateHOLFiniteState current afterGas).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source fieldBody).2.clock≤300*length.toNat+180+price := by
  have actual:=chain_nonce_prefix_cost data (180*length.toNat+113+price) (by
    intro current next
    have fees:=fee_prefix_cost next (nonce_index_bound tag) (60*length.toNat+21+price) (by
      intro gasEntry gasData
      exact gas_prefix_cost gasData (fee_index_bound tag) price tail)
    omega)
  omega

/-- Connect the original decoder entry all the way through actual gas
storage. The remaining price is required only on real contained field rows;
this is still a prefix composition, not a completed decoder allowance. -/
theorem body_through_gas_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record : BitVec 64)
    (entry : BlobHashes.Entry source pointer length record) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ payloadPointer payloadLength array heap count tag items,
      pointer.toNat≤payloadPointer.toNat→payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat→payloadLength.toNat≤length.toNat→
      FieldState current payloadPointer payloadLength record array heap count tag (gasIndex tag) items→
      current.clock-(evaluateHOLFiniteState current afterGas).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤431*length.toNat+712+price := by
  have actual:=body_rows_cost source pointer length record entry (300*length.toNat+180+price) (by
    intro parsed array tag answer selected payloadPointer payloadLength lower endpoint bounded current heap count items rows arity frame arrayCell indexCell wordCell
    let prepared : FieldState current payloadPointer payloadLength record array heap count tag 0#64 items:=⟨rows,arity,arrayCell,indexCell⟩
    have fieldPrice:=fields_through_gas_cost prepared price (by
      intro final next
      exact tail final payloadPointer payloadLength array heap count tag items lower endpoint bounded next)
    omega)
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.gas_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.gas_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.gas_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonce_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fee_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.gas_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_through_gas_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_through_gas_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Original two-argument field readers share the real array/index ABI. -/
theorem field_pair_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code)
    (kind : TransactionFields.Kind) (two : kind=.bytes ∨ kind=.list ∨ kind=.destination) (array index : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString (TransactionFields.name kind)) [.val (.word array),.val (.word index)]=
      some (TransactionFields.body kind,callee,TransactionFields.resultShape kind) ∧
      callee.lookup (ofString "arr")=some (.val (.word array)) ∧ callee.lookup (ofString "i")=some (.val (.word index)) := by
  rcases two with rfl|rfl|rfl
  all_goals exact word_pair_environment source.code.lookup _ (ofString "arr") (ofString "i") _ _ array index (by decide) (TransactionFields.original_code _ source.code installed)

/-- Normal assigned two-argument field calls retain the exact observed
return shape and the scratch-external row/record state. -/
theorem FieldState.assigned_field_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : TransactionFields.Kind)
    (two : kind=.bytes ∨ kind=.list ∨ kind=.destination) (selectedIndex : BitVec 64) (active : selectedIndex.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) (name : String) (arguments : List (ExpHOL 64))
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString (TransactionFields.name kind)) arguments)=(none,target)) :
    ∃ child value,target=CallNormal.continuationEntry source child name value ∧ FieldState target pointer length record array heap count tag index items ∧
      Rlp.CurrentItem.Frame source target ∧ shapeEqHOL (shapeOfHOLExact value) (TransactionFields.resultShape kind)=true := by
  obtain ⟨callee,called,aCell,iCell⟩:=field_pair_environment source data.data.rows.arena.code kind two array selectedIndex
  obtain ⟨funded,values,body,actual,shape,child,value,argsRead,lookup,bodyRun,checked,endpoint⟩:=CallNormal.local_data source target (ofString name) _ arguments normal
  have valueEq:=Option.some.inj (argsRead.symm.trans args)
  subst values
  have same:=Option.some.inj (lookup.symm.trans called)
  have bodyEq:=congrArg Prod.fst same
  have actualEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change body=TransactionFields.body kind at bodyEq
  change actual=callee at actualEq
  change shape=TransactionFields.resultShape kind at shapeEq
  subst body actual shape
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have frame:=TransactionFields.body_normal_frame (callEntryStateHOLFinite source callee) child kind _ _ row.arena row.fits row.arguments value bodyRun
  have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
  refine ⟨child,value,endpoint,?_,?_,checked⟩
  · rw [endpoint]
    exact data.reader_resume name value notLst notTx notType notCount notArr notK callerFrame
  · exact callerFrame.of_erase rfl (by rw [endpoint]; rfl)

theorem FieldState.field_call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : TransactionFields.Kind)
    (two : kind=.bytes ∨ kind=.list ∨ kind=.destination) (selectedIndex : BitVec 64) (active : selectedIndex.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) (name : String) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString (TransactionFields.name kind)) arguments)).2.clock≤60*item.size+12 := by
  obtain ⟨callee,called,aCell,iCell⟩:=field_pair_environment source data.data.rows.arena.code kind two array selectedIndex
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have actual:=ClockCost.assigned_current source (some (.local,ofString name)) _ arguments _ (TransactionFields.body kind) callee (TransactionFields.resultShape kind)
    (60*item.total.toNat+11) args called (TransactionFields.body_cost (callEntryStateHOLFinite source callee) kind _ _ row.arena row.fits row.arguments)
  have span:=data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected (by
    have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega)
  rw [span.1] at actual
  omega

def destinationChoice : ProgHOL 64:=match afterGas with | .seq first _=>first | _=>.skip
def destinationSuffix : ProgHOL 64:=match afterGas with | .seq _ rest=>rest | _=>.skip
def afterDestination : ProgHOL 64:=match destinationSuffix with | .seq _ (.seq _ rest)=>rest | _=>.skip
def destinationFixedArguments : List (ExpHOL 64):=[localVar "arr",localVar "k",.const 20#64]
def fieldPairArguments : List (ExpHOL 64):=[localVar "arr",localVar "k"]
def destinationFixedCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "tx_fixed_bytes") destinationFixedArguments
def destinationToCall : ProgHOL 64:=.call (some (some (.local,ofString "w"),none)) (ofString "tx_to_item") fieldPairArguments

set_option maxRecDepth 100000 in
theorem destination_shapes : afterGas=.seq destinationChoice destinationSuffix ∧
    destinationChoice=.ite (.cmp .notLower (localVar "t") (.const 3#64)) destinationFixedCall destinationToCall ∧
    destinationSuffix=.seq (fieldStore 152 "w") (.seq (indexAdvance 1#64) afterDestination) := by
  simp (maxSteps:=1000000) only [destinationChoice,destinationSuffix,afterDestination,destinationFixedCall,destinationToCall,destinationFixedArguments,fieldPairArguments,
    afterGas,afterFees,fieldStore,indexAdvance,afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,
    afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,
    body,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.destination_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) destinationFixedArguments=some (fieldReaderValues .fixed array index 20#64 0#64) ∧
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) fieldPairArguments=some [.val (.word array),.val (.word index)] := by
  simp [destinationFixedArguments,fieldPairArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell]

theorem FieldState.destination_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤5) :
    source.clock-(evaluateHOLFiniteState source destinationChoice).2.clock≤60*length.toNat+12 := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have fixed:=data.reader_call_cost .fixed index 20#64 0#64 active item selected "w" destinationFixedArguments data.destination_arguments.1
  have dest:=data.field_call_cost .destination (Or.inr (Or.inr rfl)) index active item selected "w" fieldPairArguments data.destination_arguments.2
  have first : source.clock-(evaluateHOLFiniteState source destinationFixedCall).2.clock≤60*length.toNat+12:=by
    change source.clock-(evaluateHOLFiniteState source destinationFixedCall).2.clock≤60*item.size+12 at fixed
    omega
  have second : source.clock-(evaluateHOLFiniteState source destinationToCall).2.clock≤60*length.toNat+12:=by
    change source.clock-(evaluateHOLFiniteState source destinationToCall).2.clock≤60*item.size+12 at dest
    omega
  rw [destination_shapes.2.1]
  simpa only [Nat.max_self] using ClockCost.conditional_current source _ destinationFixedCall destinationToCall _ _ first second

theorem FieldState.destination_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤5)
    (normal : evaluateHOLFiniteState source destinationChoice=(none,target)) :
    ∃ value,Nonempty (FieldState target pointer length record array heap count tag index items) ∧
      target.locals.lookup (ofString "w")=some value ∧ shapeEqHOL (shapeOfHOLExact value) .one=true := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  rw [destination_shapes.2.1] at normal
  rcases conditional_none source target _ destinationFixedCall destinationToCall normal with fixedRun|destRun
  · obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_reader_normal .fixed index 20#64 0#64 active item selected "w" destinationFixedArguments
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.destination_arguments.1 fixedRun
    refine ⟨value,⟨next⟩,?_,checked⟩
    rw [endpoint]
    simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · obtain ⟨child,value,endpoint,next,frame,checked⟩:=data.assigned_field_normal .destination (Or.inr (Or.inr rfl)) index active item selected "w" fieldPairArguments
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.destination_arguments.2 destRun
    refine ⟨value,⟨next⟩,?_,checked⟩
    rw [endpoint]
    simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem destination_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤5) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterDestination).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterGas).2.clock≤60*length.toNat+12+price := by
  rw [destination_shapes.1]
  apply ClockCost.sequence_reached_current source destinationChoice destinationSuffix _ price (data.destination_choice_cost small)
  intro current normal
  obtain ⟨value,⟨next⟩,cell,checked⟩:=data.destination_choice_normal small normal
  have read : eval current (localVar "w")=some value:=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have width : ∀ actual,eval current (localVar "w")=some actual→(flattenHOL actual).length≤1:=by
    intro actual actualRead
    have same:=Option.some.inj (actualRead.symm.trans read)
    rw [same]
    exact Nat.le_of_eq (AuthorizationFields.value_width .fixed value checked)
  rw [destination_shapes.2.2]
  have actual:=ClockCost.sequence_reached_current current _ (.seq (indexAdvance 1#64) afterDestination) 0 price (ClockCost.store current.code _ _ current rfl) (by
    intro stored storeRun
    exact (next.store_resume 152 1 (localVar "w") (by decide) width storeRun).advance_cost 1#64 afterDestination price tail)
  simpa only [Nat.zero_add,fieldStore] using actual

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.field_pair_environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.assigned_field_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.field_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.destination_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.destination_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.destination_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.destination_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.destination_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def valueArguments : List (ExpHOL 64):=[localVar "arr",localVar "k",.const 32#64]
def valueCall : ProgHOL 64:=.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") valueArguments
def afterValue : ProgHOL 64:=match afterDestination with | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem value_shape : afterDestination=.seq valueCall (.seq (fieldStore 160 "v") (.seq (indexAdvance 1#64) afterValue)) := by
  simp (maxSteps:=1000000) only [valueCall,valueArguments,afterValue,afterDestination,destinationSuffix,afterGas,afterFees,fieldStore,indexAdvance,
    afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

theorem FieldState.value_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) valueArguments=some (fieldReaderValues .wide array index 32#64 0#64) := by
  simp [valueArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell]

theorem value_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤6) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterValue).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterDestination).2.clock≤60*length.toNat+46+price := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  rw [value_shape]
  have actual:=data.read_store_cost .wide index 32#64 0#64 active item selected "v" valueArguments 160 (by decide)
    (.seq (indexAdvance 1#64) afterValue) price (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.value_arguments (by
      intro current next
      exact next.advance_cost 1#64 afterValue price tail)
  change source.clock-(evaluateHOLFiniteState source (.seq valueCall (.seq (fieldStore 160 "v") (.seq (indexAdvance 1#64) afterValue)))).2.clock≤60*item.size+46+price at actual
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.value_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.value_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.value_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real scoped bytes/list read exposes the payload from that SAME normal
callee return. Its checked containment supplies later data/list work. -/
theorem FieldState.scoped_pair_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : TransactionFields.Kind)
    (paired : kind=.bytes ∨ kind=.list) (selectedIndex : BitVec 64) (active : selectedIndex.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (price : Nat)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)])
    (tail : ∀ child header payload flag,
      Rlp.Item.Valid (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) header payload flag)→
      let ready:=CallNormal.continuationEntry source child name (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload)
      FieldState ready pointer length record array heap count tag index items→Rlp.CurrentItem.Frame source ready→
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Slices.resultShape (ofString (TransactionFields.name kind)) arguments continuation)).2.clock≤60*item.size+12+price := by
  have two : kind=.bytes ∨ kind=.list ∨ kind=.destination:=by rcases paired with first|last; exact Or.inl first; exact Or.inr (Or.inl last)
  obtain ⟨callee,called,aCell,iCell⟩:=field_pair_environment source data.data.rows.arena.code kind two array selectedIndex
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  have actual:=ClockCost.scoped_reached_current source name Rlp.Slices.resultShape _ arguments _ (TransactionFields.body kind) continuation callee (TransactionFields.resultShape kind)
    (60*item.total.toNat+11) price args called (TransactionFields.body_cost (callEntryStateHOLFinite source callee) kind _ _ row.arena row.fits row.arguments) (by
      intro child value normal checked
      obtain ⟨header,payload,flag,valid,answer,frame⟩:=TransactionFields.body_pair_normal (callEntryStateHOLFinite source callee) child kind _ _
        (Or.inr paired) row.arena row.fits row.arguments value normal
      have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
      have next:=data.reader_resume name value notLst notTx notType notCount notArr notK callerFrame
      have readyFrame : Rlp.CurrentItem.Frame source (CallNormal.continuationEntry source child name value):=callerFrame.of_erase rfl rfl
      rw [answer] at next readyFrame ⊢
      exact tail child header payload flag valid next readyFrame)
  have span:=data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected (by
    have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega)
  rw [span.1] at actual
  omega

def pairStores (name : String) (first last : Nat) (continuation : ProgHOL 64) : ProgHOL 64:=
  .seq (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 first)]) (.rfield 0 (localVar name)))
    (.seq (.store (.op .add [localVar "tx",.const (BitVec.ofNat 64 last)]) (.rfield 1 (localVar name))) continuation)

/-- The two original pointer/length stores preserve the field model from
 their own finite writes, before charging only their actual continuation. -/
theorem FieldState.pair_stores_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (name : String) (valuePointer valueLength : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (Rlp.Slices.result valuePointer valueLength))
    (first last : Nat) (firstRoom : first+8≤400) (lastRoom : last+8≤400) (continuation : ProgHOL 64) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag index items→
      current.clock-(evaluateHOLFiniteState current continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (pairStores name first last continuation)).2.clock≤price := by
  have firstRead : eval source (.rfield 0 (localVar name))=some (.val (.word valuePointer)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell,Rlp.Slices.result]
  have firstWidth : ∀ actual,eval source (.rfield 0 (localVar name))=some actual→(flattenHOL actual).length≤1:=by
    intro actual read
    have same:=Option.some.inj (read.symm.trans firstRead)
    rw [same]
    simp [flattenHOL]
  unfold pairStores
  have actual:=ClockCost.sequence_reached_current source _ _ 0 price (ClockCost.store source.code _ _ source rfl) (by
    intro stored storeRun
    have next:=data.store_resume first 1 (.rfield 0 (localVar name)) firstRoom firstWidth storeRun
    have physical:=store_none_frame source stored _ _ storeRun
    have nextCell : stored.locals.lookup (ofString name)=some (Rlp.Slices.result valuePointer valueLength):=by rw [physical]; exact cell
    have lastRead : eval stored (.rfield 1 (localVar name))=some (.val (.word valueLength)):=by
      simp [eval,evalHOLExact,toExact,localVar,nextCell,Rlp.Slices.result]
    have lastWidth : ∀ actual,eval stored (.rfield 1 (localVar name))=some actual→(flattenHOL actual).length≤1:=by
      intro actual read
      have same:=Option.some.inj (read.symm.trans lastRead)
      rw [same]
      simp [flattenHOL]
    have second:=ClockCost.sequence_reached_current stored _ continuation 0 price (ClockCost.store stored.code _ _ stored rfl) (by
      intro current lastRun
      exact tail current (next.store_resume last 1 (.rfield 1 (localVar name)) lastRoom lastWidth lastRun))
    simpa only [Nat.zero_add] using second)
  simpa only [Nat.zero_add] using actual

def dataStores : ProgHOL 64:=match afterValue with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterData : ProgHOL 64:=match dataStores with | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem data_shape : afterValue=.decCall (ofString "data") Rlp.Slices.resultShape (ofString "tx_bytes_item") fieldPairArguments dataStores ∧
    dataStores=pairStores "data" 192 200 (.seq (indexAdvance 1#64) afterData) := by
  simp (maxSteps:=1000000) only [dataStores,afterData,pairStores,Rlp.Slices.resultShape,fieldPairArguments,afterValue,afterDestination,destinationSuffix,
    afterGas,afterFees,indexAdvance,afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,
    afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,
    afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem data_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤7) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (index+1#64) items→
      current.clock-(evaluateHOLFiniteState current afterData).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterValue).2.clock≤60*length.toNat+12+price := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  rw [data_shape.1]
  have actual:=data.scoped_pair_cost .bytes (Or.inl rfl) index active item selected "data" fieldPairArguments dataStores price
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.destination_arguments.2 (by
      intro child header payload flag valid
      dsimp only
      intro prepared frame
      let ready:=CallNormal.continuationEntry source child "data" (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items index.toNat+header) payload)
      have cell : ready.locals.lookup (ofString "data")=some (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items index.toNat+header) payload):=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      rw [data_shape.2]
      apply prepared.pair_stores_cost "data" _ _ cell 192 200 (by decide) (by decide) _ price
      intro current next
      exact next.advance_cost 1#64 afterData price tail)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "data") Rlp.Slices.resultShape (ofString "tx_bytes_item") fieldPairArguments dataStores)).2.clock≤60*item.size+12+price at actual
  omega

def destinationIndex (tag : BitVec 64) : BitVec 64:=gasIndex tag+1#64
def valueIndex (tag : BitVec 64) : BitVec 64:=destinationIndex tag+1#64
def dataIndex (tag : BitVec 64) : BitVec 64:=valueIndex tag+1#64

theorem destination_index_bound (tag : BitVec 64) : (destinationIndex tag).toNat≤6 := by
  have small:=gas_index_bound tag
  unfold destinationIndex
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem value_index_bound (tag : BitVec 64) : (valueIndex tag).toNat≤7 := by
  have small:=destination_index_bound tag
  unfold valueIndex
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem data_index_bound (tag : BitVec 64) : (dataIndex tag).toNat≤8 := by
  have small:=value_index_bound tag
  unfold dataIndex
  rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem fields_through_data_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      FieldState current pointer length record array heap count tag (dataIndex tag) items→
      current.clock-(evaluateHOLFiniteState current afterData).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source fieldBody).2.clock≤480*length.toNat+250+price := by
  have actual:=fields_through_gas_cost data (180*length.toNat+70+price) (by
    intro current next
    have dest:=destination_prefix_cost next (gas_index_bound tag) (120*length.toNat+58+price) (by
      intro valueEntry valueData
      have wide:=value_prefix_cost valueData (destination_index_bound tag) (60*length.toNat+12+price) (by
        intro dataEntry nextData
        exact data_prefix_cost nextData (value_index_bound tag) price tail)
      omega)
    omega)
  omega

theorem body_through_data_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record : BitVec 64)
    (entry : BlobHashes.Entry source pointer length record) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ payloadPointer payloadLength array heap count tag items,
      pointer.toNat≤payloadPointer.toNat→payloadPointer.toNat+payloadLength.toNat=pointer.toNat+length.toNat→payloadLength.toNat≤length.toNat→
      FieldState current payloadPointer payloadLength record array heap count tag (dataIndex tag) items→
      current.clock-(evaluateHOLFiniteState current afterData).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤611*length.toNat+782+price := by
  have actual:=body_rows_cost source pointer length record entry (480*length.toNat+250+price) (by
    intro parsed array tag answer selected payloadPointer payloadLength lower endpoint bounded current heap count items rows arity frame arrayCell indexCell wordCell
    let prepared : FieldState current payloadPointer payloadLength record array heap count tag 0#64 items:=⟨rows,arity,arrayCell,indexCell⟩
    have fieldPrice:=fields_through_data_cost prepared price (by
      intro final next
      exact tail final payloadPointer payloadLength array heap count tag items lower endpoint bounded next)
    omega)
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.scoped_pair_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.pair_stores_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.data_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.data_prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.destination_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.value_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.data_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_through_data_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_through_data_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- An actual nested decoder may allocate. Its observed persistent frame
advances this same outer field model to its real next heap while protecting
the earlier transaction record, payload and converted field table. -/
theorem FieldState.persistent_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (name : String) (value : ValueHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k") (frame : PersistentNormalFrame source target heap) :
    ∃ next,Nonempty (FieldState (CallNormal.continuationEntry source target name value) pointer length record array next count tag index items) ∧ heap.toNat≤next.toNat := by
  let ready:=CallNormal.continuationEntry source target name value
  have physical : PersistentNormalFrame source ready heap:=frame.of_erase source target source ready heap rfl rfl
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=physical.nextHeap
  have domain : ready.memaddrs=source.memaddrs:=MemoryMetadata.domain (source:=source) (target:={ready with globals:=source.globals}) physical.metadata
  have endian : ready.be=source.be:=MemoryMetadata.endian (source:=source) (target:={ready with globals:=source.globals}) physical.metadata
  have code : ready.code=source.code:=MemoryMetadata.code (source:=source) (target:={ready with globals:=source.globals}) physical.metadata
  have live:=data.data.rows.arena.of_cursors domain code (physical.globals _ (by decide)) (physical.globals _ (by decide))
  have before : pointer.toNat+length.toNat≤heap.toNat:=by
    have inputBefore:=data.data.rows.inputBefore
    have tableBefore:=data.data.rows.arrayBefore
    omega
  have fits : pointer.toNat+length.toNat<2^64:=by have bound:=data.data.rows.heapBound; omega
  have window : Rlp.Slices.Window source ready heap.toNat (2^64):=by
    intro query outside
    rcases outside with lower|upper
    · exact physical.memory query lower
    · have small:=query.isLt; omega
  have bytes:=Rlp.Slices.Window.bytes_before source ready heap.toNat (2^64) pointer length window before fits domain endian
  have records:=data.data.rows.records.of_interval source ready array pointer items (by
    rw [←data.data.rows.countExact]
    have beforeTable:=data.data.rows.arrayBefore
    have bound:=data.data.rows.heapBound
    omega) (by
      intro query lower upper
      apply physical.memory query
      rw [←data.data.rows.countExact] at upper
      have beforeTable:=data.data.rows.arrayBefore
      omega)
  let converted : Converted ready pointer length record array next count tag items:={data.data with
    rows:={data.data.rows with
      arena:=live
      listCell:=by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notLst] using data.data.rows.listCell
      itemModel:=data.data.rows.itemModel.transport source ready pointer length.toNat items length.isLt bytes
      records:=records
      arrayBefore:=Nat.le_trans data.data.rows.arrayBefore grows
      heapCell:=cell,heapArena:=arena,heapBound:=bounded,heapAligned:=aligned}
    recordCell:=by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notTx] using data.data.recordCell
    typeCell:=by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notType] using data.data.typeCell
    fieldCountCell:=by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notCount] using data.data.fieldCountCell}
  exact ⟨next,⟨converted,data.arity,
    by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notArr] using data.arrayCell,
    by simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notK] using data.indexCell⟩,grows⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.persistent_resume

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

inductive NestedDecoder where | access | blob | authorization

def nestedName : NestedDecoder→String | .access=>"decode_access_list" | .blob=>"decode_blob_hashes" | .authorization=>"decode_authorizations"
def nestedBody : NestedDecoder→ProgHOL 64 | .access=>AccessLoop.body | .blob=>BlobHashes.body | .authorization=>AuthorizationLoop.body
def nestedCoefficient : NestedDecoder→Nat | .access=>494 | .blob=>186 | .authorization=>470

theorem nested_original_code (kind : NestedDecoder) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.code.lookup (ofString (nestedName kind))=some ([(ofString "p",.one),(ofString "len",.one)],nestedBody kind,Rlp.Slices.resultShape) := by
  cases kind with
  | access=>exact AccessLoop.original_code source.code installed
  | blob=>exact BlobHashes.original_code source.code installed
  | authorization=>exact AuthorizationLoop.original_code source.code installed

theorem nested_body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : NestedDecoder) (entry : BlobHashes.Entry source pointer length heap) :
    source.clock-(evaluateHOLFiniteState source (nestedBody kind)).2.clock≤nestedCoefficient kind*length.toNat+6 := by
  cases kind with
  | access=>exact AccessLoop.body_cost entry
  | blob=>exact BlobHashes.body_cost entry
  | authorization=>exact AuthorizationLoop.body_cost entry

/-- Each original nested decoder determines its own actual returned pair
and persistent frame. The result is obtained from its observed body return. -/
theorem nested_body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : NestedDecoder) (entry : BlobHashes.Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (nestedBody kind)=(some (.returned value),target)) :
    ∃ records count,value=Rlp.Slices.result records count ∧ count.toNat≤length.toNat ∧ PersistentNormalFrame source target heap := by
  cases kind with
  | access=>
    obtain ⟨records,count,answer,⟨output⟩,frame⟩:=AccessLoop.body_normal entry value normal
    exact ⟨records,count,answer,output.countBound,frame⟩
  | blob=>
    obtain ⟨records,count,answer,bound,arena,aligned,cover,frame⟩:=BlobHashes.body_normal entry value normal
    exact ⟨records,count,answer,bound,frame⟩
  | authorization=>
    obtain ⟨records,count,answer,bound,arena,aligned,cover,frame⟩:=AuthorizationLoop.body_normal entry value normal
    exact ⟨records,count,answer,bound,frame⟩

/-- Leaving a real helper-local scope restores only its own binding. -/
def FieldState.restored {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k") :
    FieldState (restore saved name source) pointer length record array heap count tag index items := {
  data:=data.data.transport rfl (restore_lookup_other saved source name "lst" (Ne.symm notLst))
    (restore_lookup_other saved source name "tx" (Ne.symm notTx)) (restore_lookup_other saved source name "t" (Ne.symm notType))
    (restore_lookup_other saved source name "nfields" (Ne.symm notCount)) (by intros; rfl) (by intros; rfl)
  arity:=data.arity
  arrayCell:=(restore_lookup_other saved source name "arr" (Ne.symm notArr)).trans data.arrayCell
  indexCell:=(restore_lookup_other saved source name "k" (Ne.symm notK)).trans data.indexCell }

/-- The actual same two stores expose their real continuing state. -/
theorem FieldState.pair_stores_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (name : String) (valuePointer valueLength : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (Rlp.Slices.result valuePointer valueLength))
    (first last : Nat) (firstRoom : first+8≤400) (lastRoom : last+8≤400) (continuation : ProgHOL 64)
    (normal : evaluateHOLFiniteState source (pairStores name first last continuation)=(none,target)) :
    ∃ current,Nonempty (FieldState current pointer length record array heap count tag index items) ∧ evaluateHOLFiniteState current continuation=(none,target) := by
  have firstRead : eval source (.rfield 0 (localVar name))=some (.val (.word valuePointer)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell,Rlp.Slices.result]
  have firstWidth : ∀ actual,eval source (.rfield 0 (localVar name))=some actual→(flattenHOL actual).length≤1:=by
    intro actual read
    have same:=Option.some.inj (read.symm.trans firstRead)
    rw [same]
    simp [flattenHOL]
  unfold pairStores at normal
  obtain ⟨stored,storeRun,rest⟩:=sequence_none source target _ _ normal
  have next:=data.store_resume first 1 (.rfield 0 (localVar name)) firstRoom firstWidth storeRun
  have physical:=store_none_frame source stored _ _ storeRun
  have nextCell : stored.locals.lookup (ofString name)=some (Rlp.Slices.result valuePointer valueLength):=by rw [physical]; exact cell
  have lastRead : eval stored (.rfield 1 (localVar name))=some (.val (.word valueLength)):=by
    simp [eval,evalHOLExact,toExact,localVar,nextCell,Rlp.Slices.result]
  have lastWidth : ∀ actual,eval stored (.rfield 1 (localVar name))=some actual→(flattenHOL actual).length≤1:=by
    intro actual read
    have same:=Option.some.inj (read.symm.trans lastRead)
    rw [same]
    simp [flattenHOL]
  obtain ⟨current,lastRun,continued⟩:=sequence_none stored target _ continuation rest
  exact ⟨current,⟨next.store_resume last 1 (.rfield 1 (localVar name)) lastRoom lastWidth lastRun⟩,continued⟩

/-- Invert the actual scoped list/bytes call, exposing the same payload,
caller state, continuation and lexical restoration used by its normal run. -/
theorem FieldState.scoped_pair_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : TransactionFields.Kind)
    (paired : kind=.bytes ∨ kind=.list) (selectedIndex : BitVec 64) (active : selectedIndex.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)])
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Slices.resultShape (ofString (TransactionFields.name kind)) arguments continuation)=(none,target)) :
    ∃ child header payload flag inner,
      Rlp.Item.Valid (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) header payload flag) ∧
      Nonempty (FieldState (CallNormal.continuationEntry source child name (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload)) pointer length record array heap count tag index items) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source child name (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload)) continuation=(none,inner) ∧ target=restore source name inner := by
  have two : kind=.bytes ∨ kind=.list ∨ kind=.destination:=by rcases paired with first|last; exact Or.inl first; exact Or.inr (Or.inl last)
  obtain ⟨callee,called,aCell,iCell⟩:=field_pair_environment source data.data.rows.arena.code kind two array selectedIndex
  have row:=data.data.row selectedIndex active item selected callee aCell iCell
  obtain ⟨funded,child,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target name Rlp.Slices.resultShape _ arguments _
    (TransactionFields.body kind) continuation callee (TransactionFields.resultShape kind) args called normal
  obtain ⟨header,payload,flag,valid,answer,frame⟩:=TransactionFields.body_pair_normal (callEntryStateHOLFinite source callee) child kind _ _ (Or.inr paired)
    row.arena row.fits row.arguments value bodyRun
  have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
  have next:=data.reader_resume name value notLst notTx notType notCount notArr notK callerFrame
  rw [answer] at next continued
  exact ⟨child,header,payload,flag,inner,valid,⟨next⟩,continued,endpoint⟩

def FieldState.nested_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (payloadPointer payloadLength : BitVec 64)
    (pCell : callee.lookup (ofString "p")=some (.val (.word payloadPointer))) (lenCell : callee.lookup (ofString "len")=some (.val (.word payloadLength)))
    (before : payloadPointer.toNat+payloadLength.toNat≤heap.toNat) :
    BlobHashes.Entry (callEntryStateHOLFinite source callee) payloadPointer payloadLength heap :=
  ⟨data.data.rows.arena.of_frame rfl,pCell,lenCell,data.data.rows.heapCell,data.data.rows.heapArena,data.data.rows.heapBound,data.data.rows.heapAligned,before⟩

/-- Normal nested returns give the same pair and the real next outer heap. -/
theorem FieldState.nested_return {source child : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : NestedDecoder) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (payloadPointer payloadLength : BitVec 64)
    (pCell : callee.lookup (ofString "p")=some (.val (.word payloadPointer))) (lenCell : callee.lookup (ofString "len")=some (.val (.word payloadLength)))
    (before : payloadPointer.toNat+payloadLength.toNat≤heap.toNat) (name : String) (value : ValueHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) (nestedBody kind)=(some (.returned value),child)) :
    ∃ records itemCount next,value=Rlp.Slices.result records itemCount ∧ itemCount.toNat≤payloadLength.toNat ∧
      Nonempty (FieldState (CallNormal.continuationEntry source child name value) pointer length record array next count tag index items) ∧
      PersistentNormalFrame source (CallNormal.continuationEntry source child name value) heap := by
  obtain ⟨records,itemCount,answer,bounded,frame⟩:=nested_body_normal kind (data.nested_entry callee payloadPointer payloadLength pCell lenCell before) value normal
  have callerFrame : PersistentNormalFrame source child heap:=frame.of_erase _ _ source child heap rfl rfl
  obtain ⟨next,prepared,grows⟩:=data.persistent_resume name value notLst notTx notType notCount notArr notK callerFrame
  exact ⟨records,itemCount,next,answer,bounded,prepared,callerFrame.of_erase _ _ _ _ heap rfl rfl⟩

theorem FieldState.scoped_nested_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : NestedDecoder) (payloadPointer payloadLength : BitVec 64)
    (before : payloadPointer.toNat+payloadLength.toNat≤heap.toNat) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (price : Nat)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values payloadPointer payloadLength))
    (tail : ∀ child records itemCount next,itemCount.toNat≤payloadLength.toNat→
      let ready:=CallNormal.continuationEntry source child name (Rlp.Slices.result records itemCount)
      FieldState ready pointer length record array next count tag index items→PersistentNormalFrame source ready heap→
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Slices.resultShape (ofString (nestedName kind)) arguments continuation)).2.clock≤nestedCoefficient kind*payloadLength.toNat+7+price := by
  obtain ⟨callee,called,pCell,lenCell⟩:=word_pair_environment source.code.lookup _ (ofString "p") (ofString "len") (nestedBody kind) Rlp.Slices.resultShape
    payloadPointer payloadLength (by decide) (nested_original_code kind source data.data.rows.arena.code)
  have actual:=ClockCost.scoped_reached_current source name Rlp.Slices.resultShape _ arguments _ (nestedBody kind) continuation callee Rlp.Slices.resultShape
    (nestedCoefficient kind*payloadLength.toNat+6) price args called (nested_body_cost kind (data.nested_entry callee payloadPointer payloadLength pCell lenCell before)) (by
      intro child value normal checked
      obtain ⟨records,itemCount,next,answer,bounded,⟨prepared⟩,frame⟩:=data.nested_return kind callee payloadPointer payloadLength pCell lenCell before name value
        notLst notTx notType notCount notArr notK normal
      rw [answer] at prepared frame ⊢
      exact tail child records itemCount next bounded prepared frame)
  omega

theorem FieldState.scoped_nested_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : NestedDecoder) (payloadPointer payloadLength : BitVec 64)
    (before : payloadPointer.toNat+payloadLength.toNat≤heap.toNat) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (notLst : ofString name≠ofString "lst") (notTx : ofString name≠ofString "tx") (notType : ofString name≠ofString "t") (notCount : ofString name≠ofString "nfields")
    (notArr : ofString name≠ofString "arr") (notK : ofString name≠ofString "k")
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values payloadPointer payloadLength))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Rlp.Slices.resultShape (ofString (nestedName kind)) arguments continuation)=(none,target)) :
    ∃ child records itemCount next inner,itemCount.toNat≤payloadLength.toNat ∧
      Nonempty (FieldState (CallNormal.continuationEntry source child name (Rlp.Slices.result records itemCount)) pointer length record array next count tag index items) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source child name (Rlp.Slices.result records itemCount)) continuation=(none,inner) ∧ target=restore source name inner := by
  obtain ⟨callee,called,pCell,lenCell⟩:=word_pair_environment source.code.lookup _ (ofString "p") (ofString "len") (nestedBody kind) Rlp.Slices.resultShape
    payloadPointer payloadLength (by decide) (nested_original_code kind source data.data.rows.arena.code)
  obtain ⟨funded,child,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target name Rlp.Slices.resultShape _ arguments _
    (nestedBody kind) continuation callee Rlp.Slices.resultShape args called normal
  obtain ⟨records,itemCount,next,answer,bounded,prepared,frame⟩:=data.nested_return kind callee payloadPointer payloadLength pCell lenCell before name value
    notLst notTx notType notCount notArr notK bodyRun
  rw [answer] at prepared continued
  exact ⟨child,records,itemCount,next,inner,bounded,prepared,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nested_original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nested_body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nested_body_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.restored
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.pair_stores_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.scoped_pair_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.nested_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.nested_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.scoped_nested_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.scoped_nested_normal

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

abbrev FieldNameSafe (name : String) : Prop:=ofString name≠ofString "lst" ∧ ofString name≠ofString "tx" ∧ ofString name≠ofString "t" ∧
  ofString name≠ofString "nfields" ∧ ofString name≠ofString "arr" ∧ ofString name≠ofString "k"
def pairArguments (name : String) : List (ExpHOL 64):=[.rfield 0 (localVar name),.rfield 1 (localVar name)]
def listProgram (kind : NestedDecoder) (inputName outputName : String) (arguments : List (ExpHOL 64)) (first last : Nat) (amount : BitVec 64) : ProgHOL 64:=
  .decCall (ofString inputName) Rlp.Slices.resultShape (ofString "tx_list_item") arguments
    (.decCall (ofString outputName) Rlp.Slices.resultShape (ofString (nestedName kind)) (pairArguments inputName)
      (pairStores outputName first last (indexAdvance amount)))

/-- The actual selected encoded field lies entirely inside the payload. -/
theorem FieldState.item_span {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selectedIndex : BitVec 64)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) :
    item.total.toNat=item.size ∧ (Rlp.Slices.itemPointer pointer items selectedIndex.toNat).toNat+item.total.toNat≤pointer.toNat+length.toNat := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.data.rows.inputBefore; have upper:=array.isLt; omega
  have span:=data.data.rows.itemModel.at_span source pointer length.toNat items selectedIndex.toNat item selected fits
  obtain ⟨offset,path,bounded,valid,encoded⟩:=data.data.rows.itemModel.at source pointer length.toNat items selectedIndex.toNat item selected
  have number : (Rlp.Slices.itemPointer pointer items selectedIndex.toNat).toNat=pointer.toNat+offset:=by
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact ⟨span.1,by rw [number,span.1]; omega⟩

/-- The SAME observed list-reader result supplies its contained nested
payload and a genuine entry before the current covering heap. -/
theorem FieldState.payload_span {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selectedIndex : BitVec 64)
    (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item) (header payload flag : BitVec 64)
    (valid : Rlp.Item.Valid (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) item.total.toNat
      (Rlp.Item.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat) header payload flag)) :
    payload.toNat≤item.size ∧ (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header).toNat+payload.toNat≤heap.toNat := by
  have span:=data.item_span selectedIndex item selected
  have fields:=valid.result_fields _ header payload flag item.total.toNat
  have inputBefore:=data.data.rows.inputBefore
  have tableBefore:=data.data.rows.arrayBefore
  have bounded:=data.data.rows.heapBound
  have number : (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header).toNat=
      (Rlp.Slices.itemPointer pointer items selectedIndex.toNat).toNat+header.toNat:=by
    rw [BitVec.toNat_add_of_lt (by omega)]
  rw [number]
  omega

theorem FieldState.list_branch_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : NestedDecoder) (selectedIndex : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (inputName outputName : String) (inputSafe : FieldNameSafe inputName) (outputSafe : FieldNameSafe outputName)
    (arguments : List (ExpHOL 64)) (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)])
    (first last : Nat) (firstRoom : first+8≤400) (lastRoom : last+8≤400) (amount : BitVec 64) :
    source.clock-(evaluateHOLFiniteState source (listProgram kind inputName outputName arguments first last amount)).2.clock≤(60+nestedCoefficient kind)*item.size+19 := by
  obtain ⟨il,it,iy,ic,ia,ik⟩:=inputSafe
  obtain ⟨ol,ot,oy,oc,oa,ok⟩:=outputSafe
  unfold listProgram
  have actual:=data.scoped_pair_cost .list (Or.inr rfl) selectedIndex active item selected inputName arguments
    (.decCall (ofString outputName) Rlp.Slices.resultShape (ofString (nestedName kind)) (pairArguments inputName) (pairStores outputName first last (indexAdvance amount)))
    (nestedCoefficient kind*item.size+7)
    il it iy ic ia ik args (by
      intro child header payload flag valid
      dsimp only
      intro prepared frame
      let ready:=CallNormal.continuationEntry source child inputName (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload)
      have extent:=data.payload_span selectedIndex item selected header payload flag valid
      have nestedArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) (pairArguments inputName)=
          some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload):=by
        simp [ready,pairArguments,CallNormal.continuationEntry,Rlp.Slices.result,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,
          localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      have nested:=prepared.scoped_nested_cost kind _ payload extent.2 outputName (pairArguments inputName) (pairStores outputName first last (indexAdvance amount)) 0
        ol ot oy oc oa ok nestedArgs (by
          intro returned records itemCount next bounded
          dsimp only
          intro nextData allocated
          have cell : (CallNormal.continuationEntry ready returned outputName (Rlp.Slices.result records itemCount)).locals.lookup (ofString outputName)=some (Rlp.Slices.result records itemCount):=by
            simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
          exact nextData.pair_stores_cost outputName records itemCount cell first last firstRoom lastRoom (indexAdvance amount) 0
            (by intro current model; exact ClockCost.assign _ _ _ _ rfl))
      have budget:=Nat.mul_le_mul_left (nestedCoefficient kind) extent.1
      omega)
  simp only [TransactionFields.name] at actual
  rw [Nat.add_mul]
  omega

theorem FieldState.list_branch_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (kind : NestedDecoder) (selectedIndex : BitVec 64)
    (active : selectedIndex.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[selectedIndex.toNat]?=some item)
    (inputName outputName : String) (inputSafe : FieldNameSafe inputName) (outputSafe : FieldNameSafe outputName)
    (arguments : List (ExpHOL 64)) (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word array),.val (.word selectedIndex)])
    (first last : Nat) (firstRoom : first+8≤400) (lastRoom : last+8≤400) (amount : BitVec 64)
    (normal : evaluateHOLFiniteState source (listProgram kind inputName outputName arguments first last amount)=(none,target)) :
    ∃ next,Nonempty (FieldState target pointer length record array next count tag (index+amount) items) := by
  obtain ⟨il,it,iy,ic,ia,ik⟩:=inputSafe
  obtain ⟨ol,ot,oy,oc,oa,ok⟩:=outputSafe
  unfold listProgram at normal
  obtain ⟨child,header,payload,flag,inner,valid,⟨prepared⟩,nestedRun,endpoint⟩:=data.scoped_pair_normal .list (Or.inr rfl) selectedIndex active item selected inputName arguments _
    il it iy ic ia ik args normal
  let ready:=CallNormal.continuationEntry source child inputName (Rlp.Slices.result (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload)
  have extent:=data.payload_span selectedIndex item selected header payload flag valid
  have nestedArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) (pairArguments inputName)=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items selectedIndex.toNat+header) payload):=by
    simp [ready,pairArguments,CallNormal.continuationEntry,Rlp.Slices.result,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,
      localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨returned,records,itemCount,next,lastInner,bounded,⟨nextData⟩,storeRun,nestedEndpoint⟩:=prepared.scoped_nested_normal kind _ payload extent.2 outputName (pairArguments inputName)
    (pairStores outputName first last (indexAdvance amount)) ol ot oy oc oa ok nestedArgs nestedRun
  have cell : (CallNormal.continuationEntry ready returned outputName (Rlp.Slices.result records itemCount)).locals.lookup (ofString outputName)=some (Rlp.Slices.result records itemCount):=by
    simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨stored,⟨storedData⟩,advanceRun⟩:=nextData.pair_stores_normal outputName records itemCount cell first last firstRoom lastRoom (indexAdvance amount) storeRun
  obtain ⟨final⟩:=storedData.advance_normal amount advanceRun
  rw [endpoint,nestedEndpoint]
  exact ⟨next,⟨(final.restored ready outputName ol ot oy oc oa ok).restored source inputName il it iy ic ia ik⟩⟩

def accessChoice : ProgHOL 64:=match afterData with | .seq first _=>first | _=>.skip
def afterAccess : ProgHOL 64:=match afterData with | .seq _ rest=>rest | _=>.skip
def accessProgram : ProgHOL 64:=listProgram .access "al" "acc" fieldPairArguments 208 216 1#64

set_option maxRecDepth 100000 in
theorem access_shapes : afterData=.seq accessChoice afterAccess ∧ accessChoice=.ite (.cmp .notEqual (localVar "t") (.const 0#64)) accessProgram .skip := by
  simp (maxSteps:=1000000) only [accessChoice,afterAccess,accessProgram,listProgram,pairArguments,pairStores,nestedName,afterData,dataStores,afterValue,
    afterDestination,destinationSuffix,afterGas,afterFees,indexAdvance,fieldPairArguments,Rlp.Slices.resultShape,afterNonce,nonceSuffix,afterVector,
    afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,
    envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.access_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤8) :
    source.clock-(evaluateHOLFiniteState source accessChoice).2.clock≤554*length.toNat+19 := by
  have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have actual:=data.list_branch_cost .access index active item selected "al" "acc" (by decide) (by decide) fieldPairArguments data.destination_arguments.2 208 216 (by decide) (by decide) 1#64
  have branch : source.clock-(evaluateHOLFiniteState source accessProgram).2.clock≤554*length.toNat+19:=by
    change source.clock-(evaluateHOLFiniteState source accessProgram).2.clock≤554*item.size+19 at actual
    omega
  rw [access_shapes.2]
  simpa only [Nat.max_zero] using ClockCost.conditional_current source _ accessProgram .skip _ 0 branch (ClockCost.skip source.code source rfl)

theorem FieldState.access_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤8)
    (normal : evaluateHOLFiniteState source accessChoice=(none,target)) :
    ∃ next,Nonempty (FieldState target pointer length record array next count tag (index+(if tag=0#64 then 0#64 else 1#64)) items) := by
  have observed : eval source (.cmp .notEqual (localVar "t") (.const 0#64))=some (.val (.word (if tag=0#64 then 0#64 else 1#64))):=by
    by_cases zero : tag=0#64
    all_goals simp [eval,evalHOLExact,toExact,localVar,data.data.typeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  rw [access_shapes.2,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  by_cases zero : tag=0#64
  · rw [if_pos zero] at normal
    change evaluateHOLFiniteState source .skip=(none,target) at normal
    rw [evaluateHOLFiniteState_skip] at normal
    have endpoint : source=target:=congrArg Prod.snd normal
    rw [←endpoint,if_pos zero,BitVec.add_zero]
    exact ⟨heap,⟨data⟩⟩
  · rw [if_neg zero] at normal
    change evaluateHOLFiniteState source accessProgram=(none,target) at normal
    have active : index.toNat<count.toNat:=by have lower:=data.count_lower; omega
    obtain ⟨item,selected,bounded⟩:=data.select index active
    rw [if_neg zero]
    exact data.list_branch_normal .access index active item selected "al" "acc" (by decide) (by decide) fieldPairArguments data.destination_arguments.2
      208 216 (by decide) (by decide) 1#64 normal

theorem access_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤8) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ next,
      FieldState current pointer length record array next count tag (index+(if tag=0#64 then 0#64 else 1#64)) items→
      current.clock-(evaluateHOLFiniteState current afterAccess).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterData).2.clock≤554*length.toNat+19+price := by
  rw [access_shapes.1]
  apply ClockCost.sequence_reached_current source accessChoice afterAccess _ price (data.access_choice_cost small)
  intro current normal
  obtain ⟨next,⟨prepared⟩⟩:=data.access_choice_normal small normal
  exact tail current next prepared

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.item_span
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.payload_span
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.list_branch_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.list_branch_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.access_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.access_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.access_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.access_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem FieldState.tag_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selected : BitVec 64) :
    eval source (.cmp .equal (localVar "t") (.const selected))=some (.val (.word (if tag=selected then 1#64 else 0#64))):=by
  by_cases same : tag=selected
  all_goals simp [eval,evalHOLExact,toExact,localVar,data.data.typeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,same]

/-- Price only the branch that the real observed transaction type selects. -/
theorem FieldState.when_tag_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selected : BitVec 64) (program : ProgHOL 64) (price : Nat)
    (branch : tag=selected→source.clock-(evaluateHOLFiniteState source program).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.ite (.cmp .equal (localVar "t") (.const selected)) program .skip)).2.clock≤price := by
  have observed:=data.tag_test selected
  rw [evaluateHOLFiniteState_ite]
  simp only [eval] at observed
  rw [observed]
  by_cases same : tag=selected
  · rw [if_pos same]
    exact branch same
  · rw [if_neg same]
    change source.clock-(evaluateHOLFiniteState source .skip).2.clock≤price
    rw [evaluateHOLFiniteState_skip]
    change source.clock-source.clock≤price
    omega

theorem FieldState.when_tag_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (selected : BitVec 64) (program : ProgHOL 64)
    (normal : evaluateHOLFiniteState source (.ite (.cmp .equal (localVar "t") (.const selected)) program .skip)=(none,target)) :
    (tag=selected ∧ evaluateHOLFiniteState source program=(none,target)) ∨ (tag≠selected ∧ source=target) := by
  have observed:=data.tag_test selected
  rw [evaluateHOLFiniteState_ite] at normal
  simp only [eval] at observed
  rw [observed] at normal
  by_cases same : tag=selected
  · rw [if_pos same] at normal
    exact Or.inl ⟨same,normal⟩
  · rw [if_neg same] at normal
    change evaluateHOLFiniteState source .skip=(none,target) at normal
    rw [evaluateHOLFiniteState_skip] at normal
    exact Or.inr ⟨same,congrArg Prod.snd normal⟩

def blobChoice : ProgHOL 64:=match afterAccess with | .seq first _=>first | _=>.skip
def afterBlob : ProgHOL 64:=match afterAccess with | .seq _ rest=>rest | _=>.skip
def authorizationChoice : ProgHOL 64:=match afterBlob with | .seq first _=>first | _=>.skip
def afterAuthorization : ProgHOL 64:=match afterBlob with | .seq _ rest=>rest | _=>.skip
def authorizationProgram : ProgHOL 64:=listProgram .authorization "aul" "au" fieldPairArguments 272 280 1#64

set_option maxRecDepth 100000 in
theorem authorization_shapes : afterBlob=.seq authorizationChoice afterAuthorization ∧
    authorizationChoice=.ite (.cmp .equal (localVar "t") (.const 4#64)) authorizationProgram .skip := by
  simp (maxSteps:=1000000) only [authorizationChoice,afterAuthorization,authorizationProgram,listProgram,pairArguments,pairStores,nestedName,afterBlob,afterAccess,
    afterData,dataStores,afterValue,afterDestination,destinationSuffix,afterGas,afterFees,indexAdvance,fieldPairArguments,Rlp.Slices.resultShape,
    afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,afterSelection,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.authorization_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤11) :
    source.clock-(evaluateHOLFiniteState source authorizationChoice).2.clock≤530*length.toNat+19 := by
  rw [authorization_shapes.2]
  apply data.when_tag_cost 4#64 authorizationProgram (530*length.toNat+19)
  intro selectedTag
  have countNumber : count.toNat=13:=by rw [data.arity,selectedTag]; rfl
  have active : index.toNat<count.toNat:=by omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have actual:=data.list_branch_cost .authorization index active item selected "aul" "au" (by decide) (by decide) fieldPairArguments data.destination_arguments.2
    272 280 (by decide) (by decide) 1#64
  change source.clock-(evaluateHOLFiniteState source authorizationProgram).2.clock≤530*item.size+19 at actual
  omega

theorem FieldState.authorization_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤11)
    (normal : evaluateHOLFiniteState source authorizationChoice=(none,target)) :
    ∃ next,Nonempty (FieldState target pointer length record array next count tag (index+(if tag=4#64 then 1#64 else 0#64)) items) := by
  rw [authorization_shapes.2] at normal
  rcases data.when_tag_normal 4#64 authorizationProgram normal with ⟨selectedTag,branch⟩|⟨other,endpoint⟩
  · have countNumber : count.toNat=13:=by rw [data.arity,selectedTag]; rfl
    have active : index.toNat<count.toNat:=by omega
    obtain ⟨item,selected,bounded⟩:=data.select index active
    rw [if_pos selectedTag]
    exact data.list_branch_normal .authorization index active item selected "aul" "au" (by decide) (by decide) fieldPairArguments data.destination_arguments.2
      272 280 (by decide) (by decide) 1#64 branch
  · rw [←endpoint,if_neg other,BitVec.add_zero]
    exact ⟨heap,⟨data⟩⟩

theorem authorization_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤11) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ next,
      FieldState current pointer length record array next count tag (index+(if tag=4#64 then 1#64 else 0#64)) items→
      current.clock-(evaluateHOLFiniteState current afterAuthorization).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterBlob).2.clock≤530*length.toNat+19+price := by
  rw [authorization_shapes.1]
  apply ClockCost.sequence_reached_current source authorizationChoice afterAuthorization _ price (data.authorization_choice_cost small)
  intro current normal
  obtain ⟨next,⟨prepared⟩⟩:=data.authorization_choice_normal small normal
  exact tail current next prepared

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.tag_test
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.when_tag_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.when_tag_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.authorization_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.authorization_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.authorization_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.authorization_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def fieldNextArguments : List (ExpHOL 64):=[localVar "arr",.op .add [localVar "k",.const 1#64]]
def blobListProgram : ProgHOL 64:=listProgram .blob "bl" "bh" fieldNextArguments 256 264 2#64
def blobProgram : ProgHOL 64:=.seq valueCall (.seq (fieldStore 224 "v") blobListProgram)

set_option maxRecDepth 100000 in
theorem blob_shapes : afterAccess=.seq blobChoice afterBlob ∧ blobChoice=.ite (.cmp .equal (localVar "t") (.const 3#64)) blobProgram .skip := by
  simp (maxSteps:=1000000) only [blobChoice,afterBlob,blobProgram,blobListProgram,listProgram,pairArguments,pairStores,nestedName,valueCall,valueArguments,
    fieldStore,fieldNextArguments,afterAccess,afterData,dataStores,afterValue,afterDestination,destinationSuffix,afterGas,afterFees,indexAdvance,
    Rlp.Slices.resultShape,afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,afterListGuard,afterTypeStore,
    afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  all_goals trivial

theorem FieldState.field_next_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) fieldNextArguments=some [.val (.word array),.val (.word (index+1#64))] := by
  simp [fieldNextArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem FieldState.blob_choice_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤9) :
    source.clock-(evaluateHOLFiniteState source blobChoice).2.clock≤306*length.toNat+65 := by
  rw [blob_shapes.2]
  apply data.when_tag_cost 3#64 blobProgram (306*length.toNat+65)
  intro selectedTag
  have countNumber : count.toNat=14:=by rw [data.arity,selectedTag]; rfl
  have active : index.toNat<count.toNat:=by omega
  have nextNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have nextActive : (index+1#64).toNat<count.toNat:=by omega
  obtain ⟨item,selected,bounded⟩:=data.select index active
  have actual:=data.read_store_cost .wide index 32#64 0#64 active item selected "v" valueArguments 224 (by decide) blobListProgram (246*length.toNat+19)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.value_arguments (by
      intro current next
      obtain ⟨nextItem,nextSelected,nextBounded⟩:=next.select (index+1#64) nextActive
      have actualList:=next.list_branch_cost .blob (index+1#64) nextActive nextItem nextSelected "bl" "bh" (by decide) (by decide)
        fieldNextArguments next.field_next_arguments 256 264 (by decide) (by decide) 2#64
      change current.clock-(evaluateHOLFiniteState current blobListProgram).2.clock≤246*nextItem.size+19 at actualList
      omega)
  change source.clock-(evaluateHOLFiniteState source blobProgram).2.clock≤60*item.size+46+(246*length.toNat+19) at actual
  omega

theorem FieldState.blob_choice_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤9)
    (normal : evaluateHOLFiniteState source blobChoice=(none,target)) :
    ∃ next,Nonempty (FieldState target pointer length record array next count tag (index+(if tag=3#64 then 2#64 else 0#64)) items) := by
  rw [blob_shapes.2] at normal
  rcases data.when_tag_normal 3#64 blobProgram normal with ⟨selectedTag,branch⟩|⟨other,endpoint⟩
  · have countNumber : count.toNat=14:=by rw [data.arity,selectedTag]; rfl
    have active : index.toNat<count.toNat:=by omega
    have nextNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
    have nextActive : (index+1#64).toNat<count.toNat:=by omega
    obtain ⟨item,selected,bounded⟩:=data.select index active
    obtain ⟨stored,⟨prepared⟩,listRun⟩:=data.read_store_normal .wide index 32#64 0#64 active item selected "v" valueArguments 224 (by decide) blobListProgram
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) data.value_arguments branch
    obtain ⟨nextItem,nextSelected,nextBounded⟩:=prepared.select (index+1#64) nextActive
    rw [if_pos selectedTag]
    exact prepared.list_branch_normal .blob (index+1#64) nextActive nextItem nextSelected "bl" "bh" (by decide) (by decide)
      fieldNextArguments prepared.field_next_arguments 256 264 (by decide) (by decide) 2#64 listRun
  · rw [←endpoint,if_neg other,BitVec.add_zero]
    exact ⟨heap,⟨data⟩⟩

theorem blob_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤9) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ next,
      FieldState current pointer length record array next count tag (index+(if tag=3#64 then 2#64 else 0#64)) items→
      current.clock-(evaluateHOLFiniteState current afterBlob).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source afterAccess).2.clock≤306*length.toNat+65+price := by
  rw [blob_shapes.1]
  apply ClockCost.sequence_reached_current source blobChoice afterBlob _ price (data.blob_choice_cost small)
  intro current normal
  obtain ⟨next,⟨prepared⟩⟩:=data.blob_choice_normal small normal
  exact tail current next prepared

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.blob_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.field_next_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.blob_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.blob_choice_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.blob_prefix_cost

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def signatureArguments (offset : Nat) : List (ExpHOL 64):=
  [localVar "arr",if offset=0 then localVar "k" else .op .add [localVar "k",.const (BitVec.ofNat 64 offset)],.const 32#64]
def signatureStep (offset destination : Nat) (continuation : ProgHOL 64) : ProgHOL 64:=
  .seq (.call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") (signatureArguments offset))
    (.seq (fieldStore destination "v") continuation)

set_option maxRecDepth 100000 in
theorem signature_shape : afterAuthorization=signatureStep 0 288 (signatureStep 1 320 (signatureStep 2 352 (.return (localVar "tx")))) := by
  simp (maxSteps:=1000000) only [signatureStep,signatureArguments,fieldStore,afterAuthorization,afterBlob,afterAccess,afterData,dataStores,afterValue,
    afterDestination,destinationSuffix,afterGas,afterFees,afterNonce,nonceSuffix,afterVector,afterChain,fieldBody,afterArity,afterArray,afterSlices,
    afterListGuard,afterTypeStore,afterSelection,selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,
    afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    Option.map_some,localVar]
  all_goals rfl

theorem FieldState.signature_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (offset : Nat) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (signatureArguments offset)=
      some (fieldReaderValues .wide array (index+BitVec.ofNat 64 offset) 32#64 0#64) := by
  by_cases zero : offset=0
  · subst offset
    simp [signatureArguments,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell]
  · simp [signatureArguments,zero,fieldReaderValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.arrayCell,data.indexCell,
      valueIsWord,valueWord,wordOpHOL,wordOp]

theorem FieldState.signature_step_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (offset destination : Nat) (room : destination+32≤400)
    (active : (index+BitVec.ofNat 64 offset).toNat<count.toNat) (continuation : ProgHOL 64) (price : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,FieldState current pointer length record array heap count tag index items→
      current.clock-(evaluateHOLFiniteState current continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (signatureStep offset destination continuation)).2.clock≤60*length.toNat+46+price := by
  obtain ⟨item,selected,bounded⟩:=data.select (index+BitVec.ofNat 64 offset) active
  have actual:=data.read_store_cost .wide (index+BitVec.ofNat 64 offset) 32#64 0#64 active item selected "v" (signatureArguments offset) destination room continuation price
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (data.signature_arguments offset) tail
  change source.clock-(evaluateHOLFiniteState source (signatureStep offset destination continuation)).2.clock≤60*item.size+46+price at actual
  omega

/-- The original final V/R/S reads and stores use three genuine rows and
return the existing transaction pointer. All stopped paths are included. -/
theorem signature_suffix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag index : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag index items) (small : index.toNat≤12)
    (active : (index+2#64).toNat<count.toNat) :
    source.clock-(evaluateHOLFiniteState source afterAuthorization).2.clock≤180*length.toNat+138 := by
  have oneNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have twoNumber : (index+2#64).toNat=index.toNat+2:=by rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have firstActive : (index+BitVec.ofNat 64 0).toNat<count.toNat:=by
    change (index+0#64).toNat<count.toNat
    rw [BitVec.add_zero]
    omega
  have secondActive : (index+BitVec.ofNat 64 1).toNat<count.toNat:=by change (index+1#64).toNat<count.toNat; omega
  rw [signature_shape]
  have actual:=data.signature_step_cost 0 288 (by decide) firstActive
    (signatureStep 1 320 (signatureStep 2 352 (.return (localVar "tx")))) (120*length.toNat+92) (by
    intro first next
    have second:=next.signature_step_cost 1 320 (by decide) secondActive (signatureStep 2 352 (.return (localVar "tx"))) (60*length.toNat+46) (by
      intro second last
      have third:=last.signature_step_cost 2 352 (by decide) active (.return (localVar "tx")) 0 (by
        intro final prepared
        exact ClockCost.returned final.code (localVar "tx") final rfl)
      omega)
    omega)
  omega

def accessIndex (tag : BitVec 64) : BitVec 64:=dataIndex tag+(if tag=0#64 then 0#64 else 1#64)
def blobIndex (tag : BitVec 64) : BitVec 64:=accessIndex tag+(if tag=3#64 then 2#64 else 0#64)
def authorizationIndex (tag : BitVec 64) : BitVec 64:=blobIndex tag+(if tag=4#64 then 1#64 else 0#64)

theorem access_index_bound (tag : BitVec 64) : (accessIndex tag).toNat≤9 := by
  have small:=data_index_bound tag
  unfold accessIndex
  split_ifs
  all_goals rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; simp only [BitVec.toNat_ofNat]; omega

theorem blob_index_bound (tag : BitVec 64) : (blobIndex tag).toNat≤11 := by
  have small:=access_index_bound tag
  unfold blobIndex
  split_ifs
  all_goals rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; simp only [BitVec.toNat_ofNat]; omega

theorem authorization_index_bound (tag : BitVec 64) : (authorizationIndex tag).toNat≤12 := by
  have small:=blob_index_bound tag
  unfold authorizationIndex
  split_ifs
  all_goals rw [BitVec.toNat_add_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; simp only [BitVec.toNat_ofNat]; omega

theorem tag_cases (tag : BitVec 64) (bounded : tag.toNat≤4) : tag=0#64 ∨ tag=1#64 ∨ tag=2#64 ∨ tag=3#64 ∨ tag=4#64 := by
  have numbers : tag.toNat=0 ∨ tag.toNat=1 ∨ tag.toNat=2 ∨ tag.toNat=3 ∨ tag.toNat=4:=by omega
  rcases numbers with first|second|third|fourth|fifth
  · exact Or.inl (BitVec.eq_of_toNat_eq first)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq second))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq third)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq fourth))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq fifth))))

/-- Actual type-dependent field advances leave exactly three signature
rows: k6/8/9/11/10 for types0/1/2/3/4, respectively. -/
theorem signature_rows_active (tag : BitVec 64) (bounded : tag.toNat≤4) :
    (authorizationIndex tag+2#64).toNat<(fieldCount tag).toNat := by
  rcases tag_cases tag bounded with rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Complete remaining original transaction field suffix: actual access,
blob/auth branches, their allocations/stores/index changes and final V/R/S. -/
theorem remaining_fields_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag (dataIndex tag) items) :
    source.clock-(evaluateHOLFiniteState source afterData).2.clock≤1570*length.toNat+241 := by
  have actual:=access_prefix_cost data (data_index_bound tag) (1016*length.toNat+222) (by
    intro current next prepared
    have blob:=blob_prefix_cost prepared (access_index_bound tag) (710*length.toNat+157) (by
      intro authEntry nextHeap authData
      have authorization:=authorization_prefix_cost authData (blob_index_bound tag) (180*length.toNat+138) (by
        intro signatures finalHeap finalData
        apply signature_suffix_cost finalData (authorization_index_bound tag)
        rw [finalData.arity]
        exact signature_rows_active tag finalData.data.tagBound)
      omega)
    omega)
  omega

/-- Complete actual unchanged transaction field body, on the real rows
produced by its own parser/converter/arity guard. -/
theorem fields_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length record array heap count tag : BitVec 64} {items : List Rlp.ListItem}
    (data : FieldState source pointer length record array heap count tag 0#64 items) :
    source.clock-(evaluateHOLFiniteState source fieldBody).2.clock≤2050*length.toNat+491 := by
  have actual:=fields_through_data_cost data (1570*length.toNat+241) (by intro current prepared; exact remaining_fields_cost prepared)
  omega

set_option maxRecDepth 100000 in
/-- Complete source call/loop allowance for the ORIGINAL current decoder.
No future field, nested-list, signature, allocation or return premise remains.
This is not yet a uniform whole-main TARGET-step theorem. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length record : BitVec 64)
    (entry : BlobHashes.Entry source pointer length record) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2181*length.toNat+1023 := by
  have actual:=body_rows_cost source pointer length record entry (2050*length.toNat+491) (by
    intro parsed array tag answer selected payloadPointer payloadLength lower endpoint bounded current heap count items rows arity frame arrayCell indexCell wordCell
    let prepared : FieldState current payloadPointer payloadLength record array heap count tag 0#64 items:=⟨rows,arity,arrayCell,indexCell⟩
    have fieldPrice:=fields_cost prepared
    omega)
  omega

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.signature_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.signature_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.FieldState.signature_step_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.signature_suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.access_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.blob_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.authorization_index_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.tag_cases
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.signature_rows_active
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.remaining_fields_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.body_cost


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionWrapper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_decode_transaction with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64):=[localVar "p",localVar "len"]
def handler : ProgHOL 64:=.raise (ofString "TxErr") (.op .add [.const 100#64,localVar "rc"])
def callProgram : ProgHOL 64:=.call (some (some (.local,ofString "tx"),some (ofString "RlpErr",ofString "rc",handler))) (ofString "decode_transaction_rlp") arguments

theorem body_shape : body=.dec (ofString "tx") .one (.const 0#64) (.dec (ofString "rc") .one (.const 0#64) (.seq callProgram (.return (localVar "tx")))) := by
  simp only [body,callProgram,arguments,handler,localVar,Guest.Software.guestFn_decode_transaction,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some]

/-- The real handled wrapper includes its actual RlpErr translation, local
initialization and final return on every outcome. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (entry : BlobHashes.Entry source pointer length heap) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2181*length.toNat+1024 := by
  rw [body_shape]
  apply ClockCost.declared_current source "tx" (.const 0#64) 0#64 _ (2181*length.toNat+1024) rfl
  apply ClockCost.declared_current (bind source "tx" 0#64) "rc" (.const 0#64) 0#64 _ (2181*length.toNat+1024) rfl
  let ready:=bind (bind source "tx" 0#64) "rc" 0#64
  have pCell : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,entry.pointerCell,
      show ofString "rc"≠ofString "p" from by decide,show ofString "tx"≠ofString "p" from by decide]
  have lenCell : ready.locals.lookup (ofString "len")=some (.val (.word length)):=by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,entry.lengthCell,
      show ofString "rc"≠ofString "len" from by decide,show ofString "tx"≠ofString "len" from by decide]
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) arguments=some (Rlp.Header.values pointer length):=by
    simp [arguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,pCell,lenCell]
  obtain ⟨callee,called,p,l⟩:=word_pair_environment ready.code.lookup (ofString "decode_transaction_rlp") (ofString "p") (ofString "len")
    TransactionEnvelope.body .one pointer length (by decide) (TransactionEnvelope.original_code ready.code (by exact entry.arena.code))
  have calleeEntry : BlobHashes.Entry (callEntryStateHOLFinite ready callee) pointer length heap:=
    ⟨entry.arena.of_frame rfl,p,l,entry.heapCell,entry.heapArena,entry.heapBound,entry.heapAligned,entry.inputBefore⟩
  have callPrice:=ClockCost.caught_destination_current ready (some (.local,ofString "tx")) (ofString "decode_transaction_rlp") arguments _
    TransactionEnvelope.body callee .one (ofString "RlpErr") (ofString "rc") handler (2181*length.toNat+1023) 0 args called
    (TransactionEnvelope.body_cost _ pointer length heap calleeEntry) (ClockCost.raised ready.code _ _)
  have actual:=ClockCost.sequence_current ready callProgram (.return (localVar "tx")) ((2181*length.toNat+1023)+0+1) 0 callPrice (ClockCost.returned ready.code _)
  simpa only [Nat.add_zero,Nat.add_assoc] using actual

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_transaction")=some ([(ofString "p",.one),(ofString "len",.one)],body,.one) := by
  have checked:=OriginalCode.indexed code installed 280 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_transaction) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.Software.guestFn_decode_transaction,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentVerify.TransactionWrapper

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionWrapper.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionWrapper.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionWrapper.original_code
