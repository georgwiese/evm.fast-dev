import InitECandidate.Solver.Input.CurrentVerify.DataMetadata
import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Input.VarList.RecordByteBudget
import InitECandidate.Solver.Input.VarList.RecordsFrame
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

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def test : ExpHOL 64:=.cmp .less (localVar "i") (localVar "ntx")
def loop : ProgHOL 64:=.while test iteration

/-- Actual SSZ row cells and bounded growing heap during the ORIGINAL
version check. The physical row/heap facts are current state facts, not a
promise that any later transaction decoder will return successfully. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start size : Nat) where
  index : BitVec 64
  heap : BitVec 64
  arena : Rlp.LiveArena source
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size))))
  arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size)))
  bounded : index.toNat≤VarList.decodedCount input start size
  records : VarList.Records source input pointer array start size
  arrayBefore : array.toNat+16*VarList.decodedCount input start size≤heap.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0

def LoopModel.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) (clock : Nat) :
    LoopModel {source with clock:=clock} input pointer array start size:=
  {model with arena:=model.arena.of_frame rfl}

theorem LoopModel.count_small {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) :
    VarList.decodedCount input start size<2^31:=
  (model.records.cells source input pointer array start size model.arena.domain).2.1

/-- The actual decoded pointer row is mapped independently of reading its
first payload byte, including the allowed zero-length transaction case. -/
theorem pointer_cell_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start size : Nat) (records : VarList.Records source input pointer array start size)
    (domain : source.memaddrs=InitE.ordinaryDomain) (index : Nat) (inside : index<VarList.decodedCount input start size) :
    source.memaddrs (VarList.row (VarList.decodedArray array size) index) := by
  rcases records with empty|nonempty
  · simp [VarList.decodedCount,empty] at inside
  · obtain ⟨plan,p,a,s,n,c,complete,valid⟩:=nonempty
    have ne : size≠0:=by have header:=plan.header; have positive:=plan.positive; rw [n] at header; omega
    have small : index<plan.count:=by simpa [VarList.decodedCount,ne,←c] using inside
    simpa only [VarList.decodedArray,if_neg ne,a] using plan.row_mapped source domain index small

/-- The SAME actual pointer/length row supplies both original decoder
arguments and its complete physical entry, including the current heap. -/
theorem LoopModel.decoder_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size)
    (active : model.index.toNat<VarList.decodedCount input start size) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=
      some [.val (.word (VarList.recordPointer input pointer start model.index.toNat)),
        .val (.word (VarList.recordLength input start size (VarList.decodedCount input start size) model.index.toNat))] ∧
    NestedLists.Entry source (VarList.recordPointer input pointer start model.index.toNat)
      (VarList.recordLength input start size (VarList.decodedCount input start size) model.index.toNat) model.heap := by
  have pointerStored:=model.records.pointer_cells source input pointer array start size model.index.toNat active
  obtain ⟨lengthMapped,lengthStored⟩:=(model.records.cells source input pointer array start size model.arena.domain).2.2 model.index.toNat active
  have pointerMapped:=pointer_cell_mapped source input pointer array start size model.records model.arena.domain model.index.toNat active
  have multiply : model.index*16#64=BitVec.ofNat 64 (16*model.index.toNat):=by simp [BitVec.ofNat_mul,BitVec.mul_comm]
  have pAddress : eval source (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64]])=
      some (.val (.word (VarList.row (VarList.decodedArray array size) model.index.toNat))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.arrayCell,model.indexCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,
      VarList.row,multiply]
  have nAddress : eval source (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64])=
      some (.val (.word (VarList.lengthCell (VarList.decodedArray array size) model.index.toNat))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,model.arrayCell,model.indexCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,
      VarList.row,VarList.lengthCell,multiply,BitVec.add_assoc]
  have pRead:=Witness.load_word_read source _ _ _ pAddress pointerMapped pointerStored
  have nRead:=Witness.load_word_read source _ _ _ nAddress lengthMapped lengthStored
  have geometry:=(model.records.slice_geometry source input pointer array start size model.index.toNat active).2.2.2
  refine ⟨?_,⟨model.arena,model.heapCell,model.heapArena,model.heapBound,model.heapAligned,by have before:=model.arrayBefore; omega⟩⟩
  simp only [eval] at pRead nRead
  simp [decodeArguments,evalListHOLFinite,evalListHOLExact,pRead,nRead]

/-- One actual normal iteration preserves the real row array before its
entering heap and carries the newly observed larger heap to the next row. -/
theorem LoopModel.step {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size)
    (active : model.index.toNat<VarList.decodedCount input start size)
    (normal : evaluateHOLFiniteState source iteration=(none,target)) :
    ∃ next : LoopModel target input pointer array start size,next.index=model.index+1#64 ∧ PersistentNormalFrame source target model.heap ∧ model.heap.toNat≤next.heap.toNat := by
  obtain ⟨args,physical⟩:=model.decoder_arguments active
  have frame:=iteration_normal source target _ _ model.heap physical args normal
  obtain ⟨nextHeap,heapCell,heapArena,heapBound,heapAligned,grows⟩:=frame.nextHeap
  have iCell:=iteration_advance source target model.index model.indexCell normal
  have nCell:=(iteration_flow (ofString "ntx") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).none_preserves source target normal
  have aCell:=(iteration_flow (ofString "txs") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).none_preserves source target normal
  have number : (model.index+1#64).toNat=model.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have small:=model.count_small; omega)]
    rfl
  have nextRecords:=model.records.of_before source target input pointer array start size model.heap.toNat model.arrayBefore frame.memory
  let next : LoopModel target input pointer array start size:={model with
    index:=model.index+1#64,heap:=nextHeap,arena:=frame.live_arena model.arena,indexCell:=iCell,
    countCell:=nCell.trans model.countCell,arrayCell:=aCell.trans model.arrayCell,bounded:=by rw [number]; omega,
    records:=nextRecords,arrayBefore:=Nat.le_trans model.arrayBefore grows,heapCell:=heapCell,heapArena:=heapArena,heapBound:=heapBound,heapAligned:=heapAligned }
  exact ⟨next,rfl,frame,grows⟩

/-- Actual per-row bytes plus constant decoder/predicate/loop overhead. -/
def rowPrice (input : Guest.InputBlob) (start size : Nat) (index : Nat) : Nat:=
  2187*(VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat+1027

def charge (input : Guest.InputBlob) (start size index : Nat) : Nat:=
  VarList.sumPrefix (rowPrice input start size) (VarList.decodedCount input start size)-VarList.sumPrefix (rowPrice input start size) index

theorem charge_step (input : Guest.InputBlob) (start size index : Nat) (active : index<VarList.decodedCount input start size) :
    charge input start size index=rowPrice input start size index+charge input start size (index+1) := by
  have next:=VarList.sum_prefix_mono (rowPrice input start size) (index+1) (VarList.decodedCount input start size) (by omega)
  simp only [VarList.sumPrefix] at next
  simp only [charge,VarList.sumPrefix]
  omega

theorem charge_zero (input : Guest.InputBlob) (start size : Nat) :
    charge input start size 0=2187*VarList.sumPrefix
      (fun index=>(VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat)
      (VarList.decodedCount input start size)+1027*VarList.decodedCount input start size := by
  have linear : ∀ count,VarList.sumPrefix (rowPrice input start size) count=2187*VarList.sumPrefix
      (fun index=>(VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat) count+1027*count:=by
    intro count
    induction count with
    | zero=>simp [VarList.sumPrefix]
    | succ count ih=>simp only [VarList.sumPrefix,rowPrice,ih]; omega
  simpa [charge,VarList.sumPrefix] using linear (VarList.decodedCount input start size)

theorem charge_le_zero (input : Guest.InputBlob) (start size index : Nat) : charge input start size index≤charge input start size 0 := by
  simp only [charge,VarList.sumPrefix,Nat.sub_zero]
  omega

theorem LoopModel.test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) :
    eval source test=some (.val (.word (if model.index.toNat<VarList.decodedCount input start size then 1#64 else 0#64))):=by
  have small:=model.count_small
  have number : (BitVec.ofNat 64 (VarList.decodedCount input start size)).toNat=VarList.decodedCount input start size:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have indexSmall : model.index.toNat<9223372036854775808:=by have before:=model.bounded; omega
  simp [eval,test,evalHOLExact,toExact,localVar,model.indexCell,model.countCell,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,indexSmall,
    show VarList.decodedCount input start size<9223372036854775808 from by omega]

theorem LoopModel.active {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<VarList.decodedCount input start size := by
  have expected:=model.test_read
  by_contra inactive
  rw [if_neg inactive] at expected
  have same : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero same

/-- Full ORIGINAL outer loop amortized by the real SSZ adjacent-offset byte
budget. Decoder allocation growth is carried between the actual iterations. -/
theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤charge input start size model.index.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current input pointer array start size)
  let allowance:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>charge input start size (CounterFlow.counterWord current (ofString "i")).toNat
  have allowance_model (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : LoopModel current input pointer array start size) :
      allowance current=charge input start size live.index.toNat:=by simp [allowance,CounterFlow.counterWord,live.indexCell,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤allowance current ∧
        ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ current.clock-output.2.clock+allowance output.2≤allowance current):=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=live.active word read nonzero
    let entered:=live.clocked (current.clock-1)
    obtain ⟨args,physical⟩:=entered.decoder_arguments active
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have price:=iteration_cost (decClockHOLFinite current) _ _ live.heap physical args
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤2187*(VarList.recordLength input start size (VarList.decodedCount input start size) live.index.toNat).toNat+1026 at price
    change output.2.clock≤current.clock-1 at forward
    have paid : current.clock-output.2.clock≤rowPrice input start size live.index.toNat:=by unfold rowPrice; omega
    have charged:=charge_step input start size live.index.toNat active
    refine ⟨?_,?_⟩
    · change current.clock-output.2.clock≤allowance current
      rw [allowance_model current live,charged]
      omega
    intro continuing
    have normal : output.1=none:=continuing.resolve_right ((iteration_flow (ofString "ntx") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).no_continue (decClockHOLFinite current))
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,frame,grows⟩:=entered.step active run
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have small:=live.count_small; omega)]
      rfl
    have nextNumber : next.index.toNat=live.index.toNat+1:=(congrArg BitVec.toNat indexEq).trans number
    refine ⟨⟨next⟩,?_⟩
    change current.clock-output.2.clock+allowance output.2≤allowance current
    rw [allowance_model current live,allowance_model output.2 next,nextNumber,charged]
    omega
  have priced:=ClockCost.potential_loop source.code test iteration invariant allowance step source rfl ⟨model⟩
  change source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤_
  rwa [allowance_model source model] at priced

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.LoopModel.count_small
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.pointer_cell_mapped
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.LoopModel.decoder_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.LoopModel.step
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.charge_step
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.charge_zero
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.LoopModel.test_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.loop_cost

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Real payload bytes and their four-byte offsets share one original SSZ
extent; the offset budget absorbs each iteration's fixed1027-tick overhead. -/
theorem loop_linear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤2187*size := by
  have priced:=loop_cost model
  have remaining:=charge_le_zero input start size model.index.toNat
  rw [charge_zero] at remaining
  have bytes:=model.records.byte_budget source input pointer array start size
  omega

/-- Actual normal completion retains the real transaction array, exits at
its count, and preserves the entire input/header band before the initial heap.
The observed bounded aligned final heap may be larger after every decode. -/
theorem loop_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size)
    (normal : evaluateHOLFiniteState source loop=(none,target)) :
    ∃ final : LoopModel target input pointer array start size,final.index.toNat=VarList.decodedCount input start size ∧
      PersistentNormalFrame source target model.heap ∧ model.heap.toNat≤final.heap.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel current input pointer array start size,
    PersistentNormalFrame source current model.heap ∧ model.heap.toNat≤live.heap.toNat
  have initial : invariant source:=⟨model,PersistentNormalFrame.refl source model.heap model.heapCell model.heapArena model.heapBound model.heapAligned,Nat.le_refl _⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,post)→invariant post:=by
    intro current codeEq valid word read nonzero funded post run
    obtain ⟨live,frame,before⟩:=valid
    let entered:=live.clocked (current.clock-1)
    obtain ⟨next,indexEq,nextFrame,grows⟩:=entered.step (live.active word read nonzero) run
    have realFrame : PersistentNormalFrame current post live.heap:=nextFrame.of_erase _ _ current post live.heap rfl rfl
    exact ⟨next,frame.trans source current post model.heap live.heap realFrame before,Nat.le_trans before grows⟩
  have noControl:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ((iteration_flow (ofString "ntx") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).summary current).2
  obtain ⟨final,frame,grows⟩:=loop_invariant_no_control source.code test iteration noControl invariant step source target rfl initial normal
  have exited:=loop_normal_exit test iteration (fun current=>(noControl current).1) source target normal
  have expected:=final.test_read
  have finished : final.index.toNat=VarList.decodedCount input start size:=by
    by_cases active : final.index.toNat<VarList.decodedCount input start size
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · have bound:=final.bounded; omega
  exact ⟨final,finished,frame,grows⟩

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.loop_linear
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.loop_normal

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def tail : ProgHOL 64:=match afterI with | .seq _ rest=>rest | _=>.skip

theorem setup_shapes : body=.dec (ofString "pl") .one (.load .one (Scalar.plus (localVar "si") 0)) afterPayload ∧
    afterPayload=.dec (ofString "txs") .one (.load .one (Scalar.plus (localVar "pl") 32)) afterArray ∧
    afterArray=.dec (ofString "ntx") .one (.load .one (Scalar.plus (localVar "pl") 40)) afterCount ∧
    afterCount=.dec (ofString "vh") .one (.load .one (Scalar.plus (localVar "si") 8)) afterVersionArray ∧
    afterVersionArray=.dec (ofString "nvh") .one (.load .one (Scalar.plus (localVar "si") 16)) afterVersionCount ∧
    afterVersionCount=.dec (ofString "k") .one (.const 0#64) afterK ∧
    afterK=.dec (ofString "i") .one (.const 0#64) afterI ∧
    afterI=.seq loop tail ∧
    tail=.seq (.ite (.cmp .notEqual (localVar "k") (localVar "nvh")) (.return (.const 0#64)) .skip) (.return (.const 1#64)) := by
  simp only [body,afterPayload,afterArray,afterCount,afterVersionArray,afterVersionCount,afterK,afterI,iteration,loop,test,tail,Scalar.plus,localVar,
    Guest.Software.guestFn_is_valid_versioned_hashes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  trivial

theorem tail_cost (code) : ClockCost.Bound code tail 0 := by
  rw [setup_shapes.2.2.2.2.2.2.2.2]
  exact ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code)) (ClockCost.returned code _)

theorem after_i_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size) :
    source.clock-(evaluateHOLFiniteState source afterI).2.clock≤2187*size := by
  rw [setup_shapes.2.2.2.2.2.2.2.1]
  exact ClockCost.sequence_current source loop tail (2187*size) 0 (loop_linear model) (tail_cost source.code)

/-- The actual setup reads/declares its own versioned-hash state. Failed
reads and shapes stop immediately; every reached i0 state gets the real row
model without requiring any future transaction or comparison to succeed. -/
theorem after_count_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array heap : BitVec 64) (start size : Nat)
    (arena : Rlp.LiveArena source) (records : VarList.Records source input pointer array start size)
    (arrayBefore : array.toNat+16*VarList.decodedCount input start size≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size))))) :
    source.clock-(evaluateHOLFiniteState source afterCount).2.clock≤2187*size := by
  rw [setup_shapes.2.2.2.1]
  apply ClockCost.declared_reached_current source (ofString "vh") .one _ afterVersionArray (2187*size)
  intro vh vhRead vhShape
  let vhState:=setVarHOLFinite (ofString "vh") vh source
  rw [setup_shapes.2.2.2.2.1]
  apply ClockCost.declared_reached_current vhState (ofString "nvh") .one _ afterVersionCount (2187*size)
  intro nvh nvhRead nvhShape
  let nvhState:=setVarHOLFinite (ofString "nvh") nvh vhState
  rw [setup_shapes.2.2.2.2.2.1]
  apply ClockCost.declared_current nvhState "k" (.const 0#64) 0#64 afterK (2187*size) rfl
  rw [setup_shapes.2.2.2.2.2.2.1]
  apply ClockCost.declared_current (bind nvhState "k" 0#64) "i" (.const 0#64) 0#64 afterI (2187*size) rfl
  let ready:=bind (bind nvhState "k" 0#64) "i" 0#64
  have readyArray : ready.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))):=by
    simp [ready,nvhState,vhState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,arrayCell,
      show ofString "i"≠ofString "txs" from by decide,show ofString "k"≠ofString "txs" from by decide,
      show ofString "nvh"≠ofString "txs" from by decide,show ofString "vh"≠ofString "txs" from by decide]
  have readyCount : ready.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))):=by
    simp [ready,nvhState,vhState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,countCell,
      show ofString "i"≠ofString "ntx" from by decide,show ofString "k"≠ofString "ntx" from by decide,
      show ofString "nvh"≠ofString "ntx" from by decide,show ofString "vh"≠ofString "ntx" from by decide]
  let model : LoopModel ready input pointer array start size:=⟨0#64,heap,arena.of_frame rfl,bind_lookup_same _ _ _,readyCount,readyArray,
    by simp,records,arrayBefore,heapCell,heapArena,heapBound,heapAligned⟩
  exact after_i_cost model

/-- Complete ORIGINAL versioned-hash checker on its genuine decoded input.
Both empty and nonempty transaction arrays, all decode/compare rejection paths
and exhausted clocks are covered. The SSZ transaction slice is charged once. -/
theorem body_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2187*(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566) := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  obtain ⟨heap,heapCell,heapLower,heapBound,heapAligned⟩:=data.heap
  let txs:=VarList.decodedArray array size
  let count:=BitVec.ofNat 64 (VarList.decodedCount input start size)
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by simp [eval,evalHOLExact,toExact,localVar,data.siLocal]
  have payloadRead : eval source (.load .one (Scalar.plus (localVar "si") 0))=some (.val (.word record)):=
    Witness.load_word_read source _ (si+0#64) record (Scalar.plus_read source (localVar "si") si 0 siRead)
      (AllocatedBytes.word_mapped source si 96 0 data.arena.domain data.siArena (by decide) data.siAligned (by decide))
      (by simpa using data.payloadCell)
  let plState:=bind source "pl" record
  have plRead : eval plState (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,localVar,plState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have arrayRead : eval plState (.load .one (Scalar.plus (localVar "pl") 32))=some (.val (.word txs)):=
    Witness.load_word_read plState _ (record+32#64) txs (Scalar.plus_read plState (localVar "pl") record 32 plRead)
      (AllocatedBytes.word_mapped plState record 136 32 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.txs
  let arrayState:=bind plState "txs" txs
  have nextPl : arrayState.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other plState "txs" "pl" txs (by decide)).trans (bind_lookup_same _ _ _)
  have nextRead : eval arrayState (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,toExact,localVar,nextPl]
  have countRead : eval arrayState (.load .one (Scalar.plus (localVar "pl") 40))=some (.val (.word count)):=
    Witness.load_word_read arrayState _ (record+40#64) count (Scalar.plus_read arrayState (localVar "pl") record 40 nextRead)
      (AllocatedBytes.word_mapped arrayState record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.count
  let countState:=bind arrayState "ntx" count
  have afterPrice : countState.clock-(evaluateHOLFiniteState countState afterCount).2.clock≤2187*size:=by
    apply after_count_cost countState input pointer array heap start size
      ((Rlp.LiveArena.of_startup data.arena).of_frame rfl) payload.transactions.records (by omega) heapCell
      ⟨by have lower:=data.recordInside.1; have upper:=data.recordInside.2; omega,by omega⟩ heapBound heapAligned
    · exact (bind_lookup_other arrayState "ntx" "txs" count (by decide)).trans (bind_lookup_same _ _ _)
    · exact bind_lookup_same _ _ _
  have nextPrice : arrayState.clock-(evaluateHOLFiniteState arrayState afterArray).2.clock≤2187*size:=by
    rw [setup_shapes.2.2.1]
    exact ClockCost.declared_current arrayState "ntx" _ count afterCount (2187*size) countRead afterPrice
  have arrayPrice : plState.clock-(evaluateHOLFiniteState plState afterPayload).2.clock≤2187*size:=by
    rw [setup_shapes.2.1]
    exact ClockCost.declared_current plState "txs" _ txs afterArray (2187*size) arrayRead nextPrice
  rw [setup_shapes.1]
  rw [←payload.transactions.sizeEq]
  exact ClockCost.declared_current source "pl" _ record afterPayload (2187*size) payloadRead arrayPrice

/-- A uniform concrete source allowance follows from the actual incoming
input/record/heap geometry, not a new mathematical input-length restriction. -/
theorem body_uniform {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤550369607472 := by
  have priced:=body_cost data
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  have inside:=payload.transactions.inside
  have sizeEq:=payload.transactions.sizeEq
  have before:=data.copied.beforeRecord
  have lower:=data.inputAfterWorkspace
  have recordBefore:=data.recordInside.2
  obtain ⟨heap,cell,heapLower,heapUpper,aligned⟩:=data.heap
  omega

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.setup_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_count_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.body_uniform

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real early hash mismatch returns from this iteration only AFTER the
same normal transaction decode; its actual allocation/input frame survives. -/
theorem iteration_returned_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64)
    (physical : NestedLists.Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some [.val (.word pointer),.val (.word length)])
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source iteration=(some (.returned value),target)) : PersistentNormalFrame source target heap := by
  obtain ⟨callee,called,entry⟩:=decoder_entry physical
  rw [iteration_shapes.1] at normal
  obtain ⟨funded,values,actualBody,actualCallee,actualShape,child,returned,inner,actualArgs,actualCalled,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_data source target "tx" .one (ofString "decode_transaction") decodeArguments afterDecode value normal
  have sameValues : values=[.val (.word pointer),.val (.word length)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have sameCall:=Option.some.inj (actualCalled.symm.trans called)
  cases sameCall
  obtain ⟨answer,tag,result,frame⟩:=TransactionWrapper.body_normal _ child pointer length heap entry returned bodyRun
  let ready:=CallNormal.continuationEntry source child "tx" returned
  have physicalFrame : PersistentNormalFrame source ready heap:=frame.of_erase _ _ source ready heap rfl rfl
  have arena:=physicalFrame.live_arena physical.arena
  have same:=after_decode_readonly ready.code arena.code ready rfl
  rw [continued] at same
  have whole:=physicalFrame.of_erase source ready source inner heap rfl same
  exact whole.of_erase source inner source target heap rfl (by rw [endpoint]; rfl)

/-- The actual returning outer loop may stop at any real hash mismatch.
All earlier normal decoder allocations compose with that SAME final return. -/
theorem loop_returned_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loop=(some (.returned value),target)) :
    PersistentNormalFrame source target model.heap := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : LoopModel current input pointer array start size),
      current.clock=clock→evaluateHOLFiniteState current loop=(some (.returned value),target)→PersistentNormalFrame current target live.heap:=by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro current live clockEq run
      have tested:=live.test_read
      change evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=
        some (.val (.word (if live.index.toNat<VarList.decodedCount input start size then 1#64 else 0#64))) at tested
      rw [loop,evaluateHOLFiniteState_while_total,tested] at run
      by_cases active : live.index.toNat<VarList.decodedCount input start size
      · rw [if_pos active] at run
        simp only [show (1#64 : BitVec 64)≠0#64 from by decide,↓reduceIte] at run
        by_cases zero : current.clock=0
        · rw [if_pos zero] at run
          cases run
        · rw [if_neg zero] at run
          have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
          let entered:=live.clocked (current.clock-1)
          generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) iteration=output at run forward
          obtain ⟨result,middle⟩:=output
          rw [StateSteps.fixed_clock (decClockHOLFinite current) middle result forward] at run
          have earlier : middle.clock<clock:=by change middle.clock≤current.clock-1 at forward; omega
          cases result with
          | none=>
            obtain ⟨next,indexEq,frame,grows⟩:=entered.step active computed
            have nextFrame:=ih middle.clock earlier middle next rfl run
            have firstFrame : PersistentNormalFrame current middle live.heap:=frame.of_erase _ _ current middle live.heap rfl rfl
            exact firstFrame.trans current middle target live.heap next.heap nextFrame grows
          | some result=>
            cases result with
            | returned answer=>
              have endpoint : middle=target:=congrArg Prod.snd run
              obtain ⟨args,physical⟩:=entered.decoder_arguments active
              have frame:=iteration_returned_frame (decClockHOLFinite current) middle _ _ live.heap physical args answer computed
              exact frame.of_erase _ _ current target live.heap rfl (by rw [←endpoint])
            | «continue»=>
              have stopped:=(iteration_flow (ofString "ntx") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).no_continue (decClockHOLFinite current)
              rw [computed] at stopped
              exact (stopped rfl).elim
            | «break»=>cases run
            | error=>cases run
            | timeOut=>cases run
            | exception identifier payload=>cases run
            | finalFfi event=>cases run
      · rw [if_neg active] at run
        simp only [↓reduceIte] at run
        cases run
  exact auxiliary source.clock source model rfl normal

theorem tail_readonly (code) : LocalEffects.Preserves code tail := by
  rw [setup_shapes.2.2.2.2.2.2.2.2]
  exact LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)) (LocalEffects.returned code _)

/-- Both actual ways of returning retain the original input frame: a
loop's genuine early return, or its genuine normal exit followed by the tail. -/
theorem after_i_returned_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {input : Guest.InputBlob}
    {pointer array : BitVec 64} {start size : Nat} (model : LoopModel source input pointer array start size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterI=(some (.returned value),target)) :
    PersistentNormalFrame source target model.heap := by
  rw [setup_shapes.2.2.2.2.2.2.2.1,evaluateHOLFiniteState_seq_line780] at normal
  generalize computed : evaluateHOLFiniteState source loop=output at normal
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>
    obtain ⟨final,finished,frame,grows⟩:=loop_normal model computed
    have same:=tail_readonly middle.code middle rfl
    change evaluateHOLFiniteState middle tail=(some (.returned value),target) at normal
    rw [normal] at same
    exact frame.of_erase source middle source target model.heap rfl same
  | some result=>
    have same : result=.returned value:=Option.some.inj (congrArg Prod.fst normal)
    subst result
    have frame:=loop_returned_frame model value computed
    have endpoint : middle=target:=congrArg Prod.snd normal
    simpa only [endpoint] using frame

/-- A normally returned declaration retains the same physical allocation
frame through both actual lexical entry and actual local restoration. -/
theorem declared_returned_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (shape : ShapeHOL)
    (expression : ExpHOL 64) (rest : ProgHOL 64) (heap : BitVec 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.dec (ofString name) shape expression rest)=(some (.returned value),target))
    (continued : ∀ declared inner,eval source expression=some declared→shapeEqHOL shape (shapeOfHOLExact declared)=true→
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) rest=(some (.returned value),inner)→
      PersistentNormalFrame (setVarHOLFinite (ofString name) declared source) inner heap) : PersistentNormalFrame source target heap := by
  obtain ⟨declared,inner,read,checked,run,endpoint⟩:=CallNormal.declaration_normal_entry source target name shape expression rest value normal
  have frame:=continued declared inner read checked run
  exact frame.of_erase _ _ source target heap rfl (by rw [endpoint]; rfl)

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.iteration_returned_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.loop_returned_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_i_returned_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.declared_returned_frame

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Returning through the original version-array/count/k/i declarations
retains the same earlier physical row/input band on BOTH return paths. -/
theorem after_count_returned_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array heap : BitVec 64) (start size : Nat)
    (arena : Rlp.LiveArena source) (records : VarList.Records source input pointer array start size)
    (arrayBefore : array.toNat+16*VarList.decodedCount input start size≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCount=(some (.returned value),target)) :
    PersistentNormalFrame source target heap := by
  rw [setup_shapes.2.2.2.1] at normal
  apply declared_returned_frame source target "vh" .one _ afterVersionArray heap value normal
  intro vh vhPost vhRead vhShape vhRun
  let vhState:=setVarHOLFinite (ofString "vh") vh source
  rw [setup_shapes.2.2.2.2.1] at vhRun
  apply declared_returned_frame vhState vhPost "nvh" .one _ afterVersionCount heap value vhRun
  intro nvh nvhPost nvhRead nvhShape nvhRun
  let nvhState:=setVarHOLFinite (ofString "nvh") nvh vhState
  rw [setup_shapes.2.2.2.2.2.1] at nvhRun
  obtain ⟨kPost,kRun,kEndpoint⟩:=declaration_return_word nvhState nvhPost "k" (.const 0#64) 0#64 afterK value rfl nvhRun
  rw [setup_shapes.2.2.2.2.2.2.1] at kRun
  obtain ⟨iPost,iRun,iEndpoint⟩:=declaration_return_word (bind nvhState "k" 0#64) kPost "i" (.const 0#64) 0#64 afterI value rfl kRun
  let ready:=bind (bind nvhState "k" 0#64) "i" 0#64
  have readyArray : ready.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))):=by
    simp [ready,nvhState,vhState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,arrayCell,
      show ofString "i"≠ofString "txs" from by decide,show ofString "k"≠ofString "txs" from by decide,
      show ofString "nvh"≠ofString "txs" from by decide,show ofString "vh"≠ofString "txs" from by decide]
  have readyCount : ready.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))):=by
    simp [ready,nvhState,vhState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,countCell,
      show ofString "i"≠ofString "ntx" from by decide,show ofString "k"≠ofString "ntx" from by decide,
      show ofString "nvh"≠ofString "ntx" from by decide,show ofString "vh"≠ofString "ntx" from by decide]
  let model : LoopModel ready input pointer array start size:=⟨0#64,heap,arena.of_frame rfl,bind_lookup_same _ _ _,readyCount,readyArray,
    by simp,records,arrayBefore,heapCell,heapArena,heapBound,heapAligned⟩
  have frame:=after_i_returned_frame model value iRun
  exact frame.of_erase ready iPost nvhState nvhPost heap rfl (by rw [kEndpoint,iEndpoint]; rfl)

/-- Every actual normal checker return, including an early mismatch0,
retains input/records/nonheap state and its actual bounded aligned heap.
The entering heap is obtained from the genuine decoded Data itself. -/
theorem body_returned_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ PersistentNormalFrame source target heap := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  obtain ⟨heap,heapCell,heapLower,heapBound,heapAligned⟩:=data.heap
  let txs:=VarList.decodedArray array size
  let count:=BitVec.ofNat 64 (VarList.decodedCount input start size)
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by simp [eval,evalHOLExact,toExact,localVar,data.siLocal]
  have payloadRead : eval source (.load .one (Scalar.plus (localVar "si") 0))=some (.val (.word record)):=
    Witness.load_word_read source _ (si+0#64) record (Scalar.plus_read source (localVar "si") si 0 siRead)
      (AllocatedBytes.word_mapped source si 96 0 data.arena.domain data.siArena (by decide) data.siAligned (by decide))
      (by simpa using data.payloadCell)
  let plState:=bind source "pl" record
  have plRead : eval plState (localVar "pl")=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,localVar,plState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have arrayRead : eval plState (.load .one (Scalar.plus (localVar "pl") 32))=some (.val (.word txs)):=
    Witness.load_word_read plState _ (record+32#64) txs (Scalar.plus_read plState (localVar "pl") record 32 plRead)
      (AllocatedBytes.word_mapped plState record 136 32 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.txs
  let arrayState:=bind plState "txs" txs
  have nextPl : arrayState.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other plState "txs" "pl" txs (by decide)).trans (bind_lookup_same _ _ _)
  have nextRead : eval arrayState (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,toExact,localVar,nextPl]
  have countRead : eval arrayState (.load .one (Scalar.plus (localVar "pl") 40))=some (.val (.word count)):=
    Witness.load_word_read arrayState _ (record+40#64) count (Scalar.plus_read arrayState (localVar "pl") record 40 nextRead)
      (AllocatedBytes.word_mapped arrayState record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.count
  let countState:=bind arrayState "ntx" count
  refine ⟨heap,heapCell,?_⟩
  rw [setup_shapes.1] at normal
  apply declared_returned_frame source target "pl" .one _ afterPayload heap value normal
  intro declared plPost read checked continued
  have same : declared=.val (.word record):=Option.some.inj (read.symm.trans payloadRead)
  subst declared
  change evaluateHOLFiniteState plState afterPayload=(some (.returned value),plPost) at continued
  rw [setup_shapes.2.1] at continued
  apply declared_returned_frame plState plPost "txs" .one _ afterArray heap value continued
  intro declared arrayPost read checked continued
  have same : declared=.val (.word txs):=Option.some.inj (read.symm.trans arrayRead)
  subst declared
  change evaluateHOLFiniteState arrayState afterArray=(some (.returned value),arrayPost) at continued
  rw [setup_shapes.2.2.1] at continued
  apply declared_returned_frame arrayState arrayPost "ntx" .one _ afterCount heap value continued
  intro declared countPost read checked continued
  have same : declared=.val (.word count):=Option.some.inj (read.symm.trans countRead)
  subst declared
  change evaluateHOLFiniteState countState afterCount=(some (.returned value),countPost) at continued
  apply after_count_returned_frame countState countPost input pointer array heap start size
    ((Rlp.LiveArena.of_startup data.arena).of_frame rfl) payload.transactions.records (by omega) heapCell
    ⟨by have lower:=data.recordInside.1; have upper:=data.recordInside.2; omega,by omega⟩ heapBound heapAligned
  · exact (bind_lookup_other arrayState "ntx" "txs" count (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _
  · exact continued

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.after_count_returned_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.body_returned_frame

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Same decoded main inputs survive a genuine persistent-allocation frame.
Heap growth is permitted; the actual restored SI binding is tracked separately. -/
theorem Data.of_persistent_normal {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (frame : PersistentNormalFrame source target heap) (before : boundary+32≤heap.toNat)
    (siCell : target.locals.lookup (ofString "si")=some (.val (.word si))) : Data input target pointer si record gasWord boundary := by
  have domain:=MemoryMetadata.domain (source:=source) (target:={target with globals:=source.globals}) frame.metadata
  have endian:=MemoryMetadata.endian (source:=source) (target:={target with globals:=source.globals}) frame.metadata
  have code:=MemoryMetadata.code (source:=source) (target:={target with globals:=source.globals}) frame.metadata
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  have heapAfter : NormalHeapEffects.AtLeast (boundary+32) target:=⟨next,cell,Nat.le_trans before grows,bounded,aligned⟩
  exact data.of_heap_frame domain endian code frame.globals heapAfter siCell (by
    intro query lower upper
    exact frame.memory query (by omega))

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.of_persistent_normal

namespace InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def arguments : List (ExpHOL 64):=[localVar "si"]

theorem caller_entry {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word si)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "is_valid_versioned_hashes") [.val (.word si)]=some (body,callee,.one) ∧
      Data input (callEntryStateHOLFinite source callee) pointer si record gasWord boundary := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word si)]:=by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.siLocal]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "is_valid_versioned_hashes") (ofString "si") body .one si (original_code source.code data.arena.code)
  exact ⟨callee,args,called,data.of_frame rfl cell⟩

/-- The complete real scoped helper costs one caller tick beyond its body.
This also covers every failed call/return check and exhausted clock. -/
theorem caller_cost {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString "vvh") .one (ofString "is_valid_versioned_hashes") arguments .skip)).2.clock≤550369607473 := by
  obtain ⟨callee,args,called,entry⟩:=caller_entry data
  exact ClockCost.scoped_current source (ofString "vvh") .one (ofString "is_valid_versioned_hashes") arguments [.val (.word si)] body .skip callee .one
    550369607472 0 args called (body_uniform entry) (ClockCost.skip source.code)

/-- An actually reached original caller gets the same real decoded Data
back after its checked return, with a growing heap and protected input band.
No zero-transaction or readonly-decoder assumption remains in this contract. -/
theorem caller_reached {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (actual : CallPrefix.Reaches source (.scoped (ofString "vvh") .one (ofString "is_valid_versioned_hashes") arguments) target) :
    Data input target pointer si record gasWord boundary ∧
      ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ boundary+32≤heap.toNat ∧ PersistentNormalFrame source target heap := by
  obtain ⟨callee,args,called,entry⟩:=caller_entry data
  obtain ⟨child,returned,run,endpoint⟩:=actual.scoped_known (ofString "vvh") .one (ofString "is_valid_versioned_hashes") arguments [.val (.word si)] body callee .one args called
  obtain ⟨heap,heapCell,frame⟩:=body_returned_frame entry returned run
  have actualFrame : PersistentNormalFrame source target heap:=frame.of_erase _ _ source target heap rfl (by rw [endpoint]; rfl)
  obtain ⟨initialHeap,initialCell,lower,upper,aligned⟩:=data.heap
  have same : initialHeap=heap:=by
    simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using Option.some.inj (initialCell.symm.trans heapCell)
  subst initialHeap
  have siCell : target.locals.lookup (ofString "si")=some (.val (.word si)):=by
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,data.siLocal,show ofString "vvh"≠ofString "si" from by decide]
  exact ⟨data.of_persistent_normal actualFrame lower siCell,heap,heapCell,lower,actualFrame⟩

end InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan

#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.caller_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.caller_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.VersionedHashScan.caller_reached
