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
