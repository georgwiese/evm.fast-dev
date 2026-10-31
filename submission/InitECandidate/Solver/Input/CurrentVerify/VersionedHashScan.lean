import InitECandidate.Solver.Input.CurrentVerify.TransactionDecoder
import InitECandidate.Solver.MutableTable.MemeqAnyFast32
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.Input.MemeqCode
import InitECandidate.Solver.Input.MemeqReadOnly
import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Persistent allocation preserves the actual live scratch cursors even
when its heap global advances; a startup-only scratch state is unnecessary. -/
theorem PersistentNormalFrame.live_arena {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    (frame : PersistentNormalFrame source target heap) (live : Rlp.LiveArena source) : Rlp.LiveArena target :=
  live.of_cursors (MemoryMetadata.domain (source:=source) (target:={target with globals:=source.globals}) frame.metadata)
    (MemoryMetadata.code (source:=source) (target:={target with globals:=source.globals}) frame.metadata)
    (frame.globals _ (by decide)) (frame.globals _ (by decide))

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.live_arena

namespace InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_tx_is_blob with | .function fn=>progToHOL fn.body | _=>.skip
def test : ExpHOL 64:=.cmp .equal (.load .one (Scalar.plus (localVar "tx") 0)) (.const 3#64)

theorem shape : body=.seq (.ite test (.return (.const 1#64)) .skip) (.return (.const 0#64)) := by
  simp only [body,test,Scalar.plus,localVar,Guest.Software.guestFn_tx_is_blob,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "tx_is_blob")=some ([(ofString "tx",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 789 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_tx_is_blob) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_tx_is_blob,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

theorem body_cost (code) : ClockCost.Bound code body 0 := by
  rw [shape]
  exact ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code)) (ClockCost.returned code _)

theorem readonly (code) : LocalEffects.Preserves code body := by
  rw [shape]
  exact LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)) (LocalEffects.returned code _)

/-- The actual owned decoder result determines the predicate's actual return.
A blob count is required only after this original type test returns true. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record tag : BitVec 64) (limit : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (cell : source.locals.lookup (ofString "tx")=some (.val (.word record)))
    (data : TransactionEnvelope.ReturnedTransaction source record tag limit) :
    evaluateHOLFiniteState source body=(some (.returned (.val (.word (if tag=3#64 then 1#64 else 0#64)))),emptyLocalsHOLFinite source) := by
  have localRead : eval source (localVar "tx")=some (.val (.word record)):=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have loaded : eval source (.load .one (Scalar.plus (localVar "tx") 0))=some (.val (.word tag)):=
    Witness.load_word_read source _ (record+0#64) tag (Scalar.plus_read source (localVar "tx") record 0 localRead)
      (AllocatedBytes.word_mapped source record 400 0 domain data.recordArena (by decide) data.recordAligned (by decide))
      (by simpa using data.typeStored)
  have read : eval source test=some (.val (.word (if tag=3#64 then 1#64 else 0#64))):=by
    simp only [eval] at loaded ⊢
    unfold test
    rw [evalHOLExact,loaded]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,read]
  by_cases selected : tag=3#64
  · simp [selected,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  · simp [selected,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind.readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionBlobKind.execute

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_is_valid_versioned_hashes with | .function fn=>progToHOL fn.body | _=>.skip
def afterPayload : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterArray : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def afterCount : ProgHOL 64:=match afterArray with | .dec _ _ _ rest=>rest | _=>.skip
def afterVersionArray : ProgHOL 64:=match afterCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterVersionCount : ProgHOL 64:=match afterVersionArray with | .dec _ _ _ rest=>rest | _=>.skip
def afterK : ProgHOL 64:=match afterVersionCount with | .dec _ _ _ rest=>rest | _=>.skip
def afterI : ProgHOL 64:=match afterK with | .dec _ _ _ rest=>rest | _=>.skip
def iteration : ProgHOL 64:=match afterI with | .seq (.while _ first) _=>first | _=>.skip
def afterDecode : ProgHOL 64:=match iteration with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterIsBlob : ProgHOL 64:=match afterDecode with | .decCall _ _ _ _ rest=>rest | _=>.skip
def blobChoice : ProgHOL 64:=match afterIsBlob with | .seq first _=>first | _=>.skip
def blobBranch : ProgHOL 64:=match blobChoice with | .ite _ yes _=>yes | _=>.skip
def afterBlobCount : ProgHOL 64:=match blobBranch with | .dec _ _ _ rest=>rest | _=>.skip
def blobLoop : ProgHOL 64:=match afterBlobCount with | .dec _ _ _ rest=>rest | _=>.skip
def blobStep : ProgHOL 64:=match blobLoop with | .while _ rest=>rest | _=>.skip
def blobGuard : ProgHOL 64:=.ite (.cmp .notLower (localVar "k") (localVar "nvh")) (.return (.const 0#64)) .skip
def compareLeft : ExpHOL 64:=.op .add [.load .one (Scalar.plus (localVar "tx") 256),.panop .mul [localVar "j",.const 32#64]]
def compareRight : ExpHOL 64:=.op .add [localVar "vh",.panop .mul [localVar "k",.const 32#64]]
def equalityGuard : ProgHOL 64:=.ite (.cmp .equal (localVar "eq") (.const 0#64)) (.return (.const 0#64)) .skip
def incrementK : ProgHOL 64:=.assign .local (ofString "k") (.op .add [localVar "k",.const 1#64])
def incrementJ : ProgHOL 64:=.assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])
def comparisonTail : ProgHOL 64:=.seq equalityGuard (.seq incrementK incrementJ)
def comparison : ProgHOL 64:=.decCall (ofString "eq") .one (ofString "memeq") [compareLeft,compareRight,.const 32#64] comparisonTail

theorem blob_shapes :
    blobBranch=.dec (ofString "nb") .one (.load .one (Scalar.plus (localVar "tx") 264)) afterBlobCount ∧
    afterBlobCount=.dec (ofString "j") .one (.const 0#64) blobLoop ∧
    blobLoop=.while (.cmp .less (localVar "j") (localVar "nb")) blobStep ∧
    blobStep=.seq blobGuard comparison := by
  simp only [body,afterPayload,afterArray,afterCount,afterVersionArray,afterVersionCount,afterK,afterI,iteration,afterDecode,afterIsBlob,
    blobChoice,blobBranch,afterBlobCount,blobLoop,blobStep,blobGuard,comparison,comparisonTail,compareLeft,compareRight,equalityGuard,incrementK,incrementJ,
    Scalar.plus,localVar,Guest.Software.guestFn_is_valid_versioned_hashes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  trivial

/-- Tight actual32-byte comparison allowance, including operand failures.
Only the literal n=32 is used; mapping/alignment or a future match is not assumed. -/
theorem memeq_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64)
    (name : MlS) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (quiet : ClockCost.Bound source.code continuation 0) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "memeq") [first,second,.const 32#64] continuation)).2.clock≤5 := by
  classical
  cases firstRead : eval source first with
  | none=>
    simp only [eval] at firstRead
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp [evalListHOLFinite,evalListHOLExact,firstRead]
  | some left=>
    cases secondRead : eval source second with
    | none=>
      simp only [eval] at firstRead secondRead
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead]
    | some right=>
      let actualValues : List (ValueHOL 64):=[left,right,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,.const 32#64]=some actualValues := by
        simp only [eval] at firstRead secondRead
        simp [actualValues,evalListHOLFinite,evalListHOLExact,firstRead,secondRead,evalHOLExact]
      cases left <;> cases right
      case val.val a b=>
        cases a with
        | word a=>
          cases b with
          | word b=>
            obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup a b 32 code
            exact ClockCost.scoped_current source name .one (ofString "memeq") [first,second,.const 32#64] _ Memeq32.body continuation callee .one 4 0 args called
              (MutableTable.MemeqAny.tight_body_cost (callEntryStateHOLFinite source callee) nCell) quiet
      all_goals
        have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") actualValues=none := by
          apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") actualValues).mpr
          unfold lookupCodeHOLExact
          rw [code]
          simp [actualValues,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
        simp [failed]

theorem blob_guard_flow (key : MlS) : LocalFlow key blobGuard:=.ite _ (.returned _) (.base .skip)
theorem equality_guard_flow (key : MlS) : LocalFlow key equalityGuard:=.ite _ (.returned _) (.base .skip)

theorem comparison_tail_flow (key : MlS) (notK : key≠ofString "k") (notJ : key≠ofString "j") : LocalFlow key comparisonTail:=
  .seq (equality_guard_flow key) (.seq (.base (.assign _ _ notK)) (.base (.assign _ _ notJ)))

theorem blob_step_flow (key : MlS) (notK : key≠ofString "k") (notJ : key≠ofString "j") (notEq : key≠ofString "eq") : LocalFlow key blobStep := by
  rw [blob_shapes.2.2.2]
  exact .seq (blob_guard_flow key) (.decCall _ _ _ _ notEq (comparison_tail_flow key notK notJ))

theorem blob_step_advance : CounterFlow.Advances (ofString "j") 1 blobStep := by
  rw [blob_shapes.2.2.2]
  have tailProgress : CounterFlow.Advances (ofString "j") 1 comparisonTail:=by
    have front:=CounterFlow.flow_preserved (ofString "j") equalityGuard (equality_guard_flow _)
    have middle:=CounterFlow.preserved (ofString "j") incrementK (.assign _ _ (by decide))
    have last:=CounterFlow.increment (ofString "j")
    exact CounterFlow.sequence _ _ _ 0 1 front (CounterFlow.sequence _ _ _ 0 1 middle last)
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.flow_preserved _ _ (blob_guard_flow _))
    (CounterFlow.scoped_call _ "eq" .one _ _ _ 1 (by decide) tailProgress)

theorem comparison_tail_cost (code) : ClockCost.Bound code comparisonTail 0:=
  ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code))
    (ClockCost.sequence code _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.assign code _ _))

theorem blob_step_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code blobStep 5 := by
  intro source codeEq
  rw [blob_shapes.2.2.2]
  exact ClockCost.sequence_current source blobGuard comparison 0 5
    (ClockCost.conditional source.code _ _ _ 0 0 (ClockCost.returned source.code _) (ClockCost.skip source.code) source rfl)
    (by
      intro current nextCode
      exact memeq_cost current compareLeft compareRight (ofString "eq") comparisonTail
        (by rw [nextCode,codeEq]; exact MutableTable.MemeqAny.original_code code installed) (comparison_tail_cost current.code))

/-- The actual nested signed loop costs six ticks per remaining hash,
including comparison and loop overhead, even on failed reads or early return. -/
theorem blob_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count index : BitVec 64)
    (installed : OriginalCode.Installed source.code) (small : count.toNat<2^63)
    (counter : source.locals.lookup (ofString "j")=some (.val (.word index)))
    (countCell : source.locals.lookup (ofString "nb")=some (.val (.word count))) (bounded : index.toNat≤count.toNat) :
    source.clock-(evaluateHOLFiniteState source blobLoop).2.clock≤6*(count.toNat-index.toNat) := by
  rw [blob_shapes.2.2.1]
  apply CounterFlow.loop_snapshot_cost source.code (ofString "j") (ofString "nb") (some (.val (.word count)))
    (.cmp .less (localVar "j") (localVar "nb")) blobStep 5 count.toNat (by omega) _ (blob_step_cost source.code installed)
    blob_step_advance (blob_step_flow _ (by decide) (by decide) (by decide)) source index rfl counter countCell bounded
  intro current word jCell nbCell before
  have wordSmall : word.toNat<9223372036854775808:=by omega
  simp [evalHOLFinite,evalHOLExact,toExact,localVar,jCell,nbCell,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,wordSmall,
    show count.toNat<9223372036854775808 from small]

theorem comparison_tail_readonly (code) : LocalEffects.Preserves code comparisonTail:=
  LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code))
    (LocalEffects.sequence code _ _ (LocalEffects.assign code _ _) (LocalEffects.assign code _ _))

/-- All outcomes of the original blob loop retain every nonlocal field.
Only caller-local j/k progress changes; decoding allocations occur outside it. -/
theorem blob_loop_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code blobLoop := by
  rw [blob_shapes.2.2.1]
  apply LocalEffects.loop
  rw [blob_shapes.2.2.2]
  apply LocalEffects.sequence
  · exact LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)
  · exact LocalEffects.scoped_body code _ _ _ _ comparisonTail Memeq32.formals Memeq32.body .one
      (MutableTable.MemeqAny.original_code code installed) (MutableTable.MemeqAny.readonly code) (comparison_tail_readonly code)

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.memeq_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_step_flow
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_step_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_step_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_loop_readonly

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real decoder-owned blob count supplies the original nested loop.
No current comparison or future load is assumed to succeed. -/
theorem blob_branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (limit : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cell : source.locals.lookup (ofString "tx")=some (.val (.word record)))
    (data : TransactionEnvelope.ReturnedTransaction source record 3#64 limit) (small : limit<2^63) :
    source.clock-(evaluateHOLFiniteState source blobBranch).2.clock≤6*limit := by
  obtain ⟨buffer,count,heap,pointerCell,countCell,countBound,arena,aligned,heapCell,room,bounded,heapAligned⟩:=data.blob rfl
  have localRead : eval source (localVar "tx")=some (.val (.word record)):=by simp [eval,evalHOLExact,toExact,localVar,cell]
  have countRead : eval source (.load .one (Scalar.plus (localVar "tx") 264))=some (.val (.word count)):=
    Witness.load_word_read source _ (record+264#64) count (Scalar.plus_read source (localVar "tx") record 264 localRead)
      (AllocatedBytes.word_mapped source record 400 264 domain data.recordArena (by decide) data.recordAligned (by decide)) countCell
  let nbState:=bind source "nb" count
  let jState:=bind nbState "j" 0#64
  have jCell : jState.locals.lookup (ofString "j")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have nbCell : jState.locals.lookup (ofString "nb")=some (.val (.word count)):=
    (bind_lookup_other nbState "j" "nb" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
  have loopPrice:=blob_loop_cost jState count 0#64 installed (by omega) jCell nbCell (by simp)
  have nextPrice:=ClockCost.declared_current nbState "j" (.const 0#64) 0#64 blobLoop (6*count.toNat) rfl (by simpa only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.sub_zero] using loopPrice)
  rw [blob_shapes.1]
  have allPrice:=ClockCost.declared_current source "nb" _ count afterBlobCount (6*count.toNat) countRead (by
    rw [blob_shapes.2.1]
    exact nextPrice)
  omega

theorem blob_branch_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code blobBranch := by
  rw [blob_shapes.1]
  apply LocalEffects.declared
  rw [blob_shapes.2.1]
  exact LocalEffects.declared code _ _ _ _ (blob_loop_readonly code installed)

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_branch_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_branch_readonly

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def incrementI : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def decodeArguments : List (ExpHOL 64):=[
  .load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64]]),
  .load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64])]

theorem iteration_shapes :
    iteration=.decCall (ofString "tx") .one (ofString "decode_transaction") decodeArguments afterDecode ∧
    afterDecode=.decCall (ofString "isb") .one (ofString "tx_is_blob") [localVar "tx"] afterIsBlob ∧
    afterIsBlob=.seq blobChoice incrementI ∧
    blobChoice=.ite (.cmp .notEqual (localVar "isb") (.const 0#64)) blobBranch .skip := by
  simp only [body,afterPayload,afterArray,afterCount,afterVersionArray,afterVersionCount,afterK,afterI,iteration,afterDecode,afterIsBlob,
    blobChoice,blobBranch,incrementI,decodeArguments,localVar,Guest.Software.guestFn_is_valid_versioned_hashes,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "is_valid_versioned_hashes")=some ([(ofString "si",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 792 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_is_valid_versioned_hashes) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_is_valid_versioned_hashes,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- Only a true result from the actual type predicate opens the blob branch.
All other types skip the blob fields entirely. -/
theorem blob_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record tag : BitVec 64) (limit : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cell : source.locals.lookup (ofString "tx")=some (.val (.word record)))
    (predicate : source.locals.lookup (ofString "isb")=some (.val (.word (if tag=3#64 then 1#64 else 0#64))))
    (data : TransactionEnvelope.ReturnedTransaction source record tag limit) (small : limit<2^63) :
    source.clock-(evaluateHOLFiniteState source blobChoice).2.clock≤6*limit := by
  have read : eval source (.cmp .notEqual (localVar "isb") (.const 0#64))=
      some (.val (.word (if tag=3#64 then 1#64 else 0#64))):=by
    by_cases selected : tag=3#64 <;> simp [eval,evalHOLExact,toExact,localVar,predicate,selected,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [iteration_shapes.2.2.2,evaluateHOLFiniteState_ite,read]
  by_cases selected : tag=3#64
  · simp only [if_pos selected,show (1#64 : BitVec 64)≠0#64 from by decide,↓reduceIte]
    subst tag
    exact blob_branch_cost source record limit installed domain cell data small
  · simp only [if_neg selected,↓reduceIte,evaluateHOLFiniteState_skip]
    change source.clock-source.clock≤6*limit
    omega

theorem after_is_blob_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record tag : BitVec 64) (limit : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cell : source.locals.lookup (ofString "tx")=some (.val (.word record)))
    (predicate : source.locals.lookup (ofString "isb")=some (.val (.word (if tag=3#64 then 1#64 else 0#64))))
    (data : TransactionEnvelope.ReturnedTransaction source record tag limit) (small : limit<2^63) :
    source.clock-(evaluateHOLFiniteState source afterIsBlob).2.clock≤6*limit := by
  rw [iteration_shapes.2.2.1]
  exact ClockCost.sequence_current source blobChoice incrementI (6*limit) 0
    (blob_choice_cost source record tag limit installed domain cell predicate data small) (ClockCost.assign source.code _ _)

/-- Complete actual post-decoder work, using the same returned record and
same actual tx_is_blob return. There is no empty-transaction restriction. -/
theorem after_decode_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record tag : BitVec 64) (limit : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (cell : source.locals.lookup (ofString "tx")=some (.val (.word record)))
    (data : TransactionEnvelope.ReturnedTransaction source record tag limit) (small : limit<2^63) :
    source.clock-(evaluateHOLFiniteState source afterDecode).2.clock≤6*limit+1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "tx"]=some [.val (.word record)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cell]
  obtain ⟨callee,called,txCell⟩:=word_environment source.code.lookup (ofString "tx_is_blob") (ofString "tx") TransactionBlobKind.body .one record
    (TransactionBlobKind.original_code source.code installed)
  rw [iteration_shapes.2.1]
  apply Nat.le_trans (m:=0+6*limit+1) ?_ (by omega)
  apply ClockCost.scoped_reached_current source "isb" .one (ofString "tx_is_blob") [localVar "tx"] _ TransactionBlobKind.body afterIsBlob callee .one 0 (6*limit)
    args called (TransactionBlobKind.body_cost source.code (callEntryStateHOLFinite source callee) rfl)
  intro child returned normal checked
  have expected:=TransactionBlobKind.execute (callEntryStateHOLFinite source callee) record tag limit domain txCell (data.of_erase rfl)
  rw [expected] at normal
  cases normal
  let ready:=CallNormal.continuationEntry source (emptyLocalsHOLFinite (callEntryStateHOLFinite source callee)) "isb" (.val (.word (if tag=3#64 then 1#64 else 0#64)))
  have readyTx : ready.locals.lookup (ofString "tx")=some (.val (.word record)):=by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,cell,show ofString "isb"≠ofString "tx" from by decide]
  have readyIsb : ready.locals.lookup (ofString "isb")=some (.val (.word (if tag=3#64 then 1#64 else 0#64))):=by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  exact after_is_blob_cost ready record tag limit installed domain readyTx readyIsb (data.of_erase rfl) small

theorem after_is_blob_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code afterIsBlob := by
  rw [iteration_shapes.2.2.1]
  apply LocalEffects.sequence
  · rw [iteration_shapes.2.2.2]
    exact LocalEffects.conditional code _ _ _ (blob_branch_readonly code installed) (LocalEffects.skip code)
  · exact LocalEffects.assign code _ _

theorem after_decode_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code afterDecode := by
  rw [iteration_shapes.2.1]
  exact LocalEffects.scoped_body code _ _ _ _ afterIsBlob [(ofString "tx",.one)] TransactionBlobKind.body .one
    (TransactionBlobKind.original_code code installed) (TransactionBlobKind.readonly code) (after_is_blob_readonly code installed)

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_choice_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_is_blob_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_decode_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_decode_readonly

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem blob_branch_flow (key : MlS) (notNb : key≠ofString "nb") (notJ : key≠ofString "j")
    (notK : key≠ofString "k") (notEq : key≠ofString "eq") : LocalFlow key blobBranch := by
  rw [blob_shapes.1]
  apply LocalFlow.dec _ _ _ notNb
  rw [blob_shapes.2.1]
  apply LocalFlow.dec _ _ _ notJ
  rw [blob_shapes.2.2.1]
  exact .loop _ (blob_step_flow key notK notJ notEq)

theorem blob_choice_flow (key : MlS) (notNb : key≠ofString "nb") (notJ : key≠ofString "j")
    (notK : key≠ofString "k") (notEq : key≠ofString "eq") : LocalFlow key blobChoice := by
  rw [iteration_shapes.2.2.2]
  exact .ite _ (blob_branch_flow key notNb notJ notK notEq) (.base .skip)

theorem after_decode_flow (key : MlS) (notIsb : key≠ofString "isb") (notNb : key≠ofString "nb")
    (notI : key≠ofString "i") (notJ : key≠ofString "j") (notK : key≠ofString "k") (notEq : key≠ofString "eq") : LocalFlow key afterDecode := by
  rw [iteration_shapes.2.1]
  apply LocalFlow.decCall _ _ _ _ notIsb
  rw [iteration_shapes.2.2.1]
  exact .seq (blob_choice_flow key notNb notJ notK notEq) (.base (.assign _ _ notI))

theorem iteration_flow (key : MlS) (notTx : key≠ofString "tx") (notIsb : key≠ofString "isb") (notNb : key≠ofString "nb")
    (notI : key≠ofString "i") (notJ : key≠ofString "j") (notK : key≠ofString "k") (notEq : key≠ofString "eq") : LocalFlow key iteration := by
  rw [iteration_shapes.1]
  exact .decCall _ _ _ _ notTx (after_decode_flow key notIsb notNb notI notJ notK notEq)

/-- Real early returns terminate the enclosing checker. Every actual
continuation instead advances its original i exactly once, after both scopes. -/
theorem iteration_advance : CounterFlow.Advances (ofString "i") 1 iteration := by
  rw [iteration_shapes.1]
  apply CounterFlow.scoped_call _ "tx" .one _ _ _ 1 (by decide)
  rw [iteration_shapes.2.1]
  apply CounterFlow.scoped_call _ "isb" .one _ _ _ 1 (by decide)
  rw [iteration_shapes.2.2.1]
  exact CounterFlow.sequence _ _ _ 0 1
    (CounterFlow.flow_preserved _ _ (blob_choice_flow _ (by decide) (by decide) (by decide) (by decide)))
    (CounterFlow.increment (ofString "i"))

theorem decoder_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (physical : NestedLists.Entry source pointer length heap) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "decode_transaction") [.val (.word pointer),.val (.word length)]=some (TransactionWrapper.body,callee,.one) ∧
      BlobHashes.Entry (callEntryStateHOLFinite source callee) pointer length heap := by
  obtain ⟨callee,called,p,l⟩:=word_pair_environment source.code.lookup (ofString "decode_transaction") (ofString "p") (ofString "len") TransactionWrapper.body .one pointer length
    (by decide) (TransactionWrapper.original_code source.code physical.arena.code)
  exact ⟨callee,called,⟨physical.arena.of_frame rfl,p,l,physical.heapCell,physical.heapArena,physical.heapBound,physical.heapAligned,physical.inputBefore⟩⟩

/-- Complete actual checker iteration, charged to this transaction's own
raw length. The normal decoder return supplies its real record/type/blob data;
rejecting decodes, comparisons, reads and exhausted clocks are also covered. -/
theorem iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (physical : NestedLists.Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some [.val (.word pointer),.val (.word length)]) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤2187*length.toNat+1026 := by
  obtain ⟨callee,called,entry⟩:=decoder_entry physical
  rw [iteration_shapes.1]
  have price:=ClockCost.scoped_reached_current source "tx" .one (ofString "decode_transaction") decodeArguments _ TransactionWrapper.body afterDecode callee .one
    (2181*length.toNat+1024) (6*length.toNat+1) args called (TransactionWrapper.body_cost _ pointer length heap entry) (by
      intro child returned normal checked
      obtain ⟨answer,tag,result,frame⟩:=TransactionWrapper.body_normal _ child pointer length heap entry returned normal
      subst returned
      let ready:=CallNormal.continuationEntry source child "tx" (.val (.word heap))
      have txCell : ready.locals.lookup (ofString "tx")=some (.val (.word heap)):=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      have arena:=frame.live_arena entry.arena
      have resultReady : TransactionEnvelope.ReturnedTransaction ready heap tag length.toNat:=result.of_erase rfl
      have small : length.toNat<2^63:=by have inputBefore:=physical.inputBefore; have cap:=physical.heapBound; omega
      exact after_decode_cost ready heap tag length.toNat arena.code arena.domain txCell resultReady small)
  omega

/-- Actual normal iteration may allocate. Its retained frame protects all
input/array/header words before the incoming heap and exposes the next bounded
aligned heap, rather than incorrectly claiming the decoder was read-only. -/
theorem iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (physical : NestedLists.Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some [.val (.word pointer),.val (.word length)])
    (normal : evaluateHOLFiniteState source iteration=(none,target)) : PersistentNormalFrame source target heap := by
  obtain ⟨callee,called,entry⟩:=decoder_entry physical
  rw [iteration_shapes.1] at normal
  obtain ⟨funded,child,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target "tx" .one (ofString "decode_transaction")
    decodeArguments _ TransactionWrapper.body afterDecode callee .one args called normal
  obtain ⟨answer,tag,result,frame⟩:=TransactionWrapper.body_normal _ child pointer length heap entry returned bodyRun
  let ready:=CallNormal.continuationEntry source child "tx" returned
  have physicalFrame : PersistentNormalFrame source ready heap:=frame.of_erase _ _ source ready heap rfl rfl
  have arena:=physicalFrame.live_arena physical.arena
  have same:=after_decode_readonly ready.code arena.code ready rfl
  rw [continued] at same
  have whole:=physicalFrame.of_erase source ready source inner heap rfl same
  exact whole.of_erase source inner source target heap rfl (by rw [endpoint]; rfl)

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.blob_branch_flow
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_flow
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_advance
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.decoder_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_normal
