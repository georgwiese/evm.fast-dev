import InitECandidate.Solver.Input.CurrentTable.NewScalarImage
import InitECandidate.Solver.Input.CurrentTable.NewNode.Call
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Program
import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.CurrentTable.ScalarLookup
import InitECandidate.Solver.Input.CurrentTable.Set.Guards
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual scalar constructor already supplies the first no-grow node
at every current key width, including20byte account-access keys. -/
theorem from_scalar_empty {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : New.ScalarEmpty source table key cap) : Context source table 1#64 cap := by
  exact ⟨image.domain,image.geometry.table,image.aligned,
    image.fields (table+72#64,0#64) (by simp [New.scalarWrites]),image.fields (table+64#64,1#64) (by simp [New.scalarWrites]),
    image.fields (table+80#64,cap) (by simp [New.scalarWrites]),by have lower:=image.capLower; change 1≤cap.toNat; omega⟩

end InitECandidate.Solver.Input.CurrentTable.NewNode

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Only actual scalar header fields read before the real key copy. The
node allocator may update the next-index word independently. -/
structure ScalarFields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat%8=0
  length : source.memory table=.word key
  stride : source.memory (table+8#64)=.word (New.strideWord key)
  keys : source.memory (table+32#64)=.word (New.keysPointer table)

theorem ScalarFields.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table key : BitVec 64}
    (fields : ScalarFields source table key) (same : LocalEffects.erase target=LocalEffects.erase source) : ScalarFields target table key := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact ⟨domain.trans fields.domain,fields.arena,fields.aligned,by rw [memory]; exact fields.length,
    by rw [memory]; exact fields.stride,by rw [memory]; exact fields.keys⟩

theorem ScalarFields.after_next {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table key cap : BitVec 64}
    (image : New.ScalarEmpty source table key cap) : ScalarFields (New.putField source table 64 2#64) table key := by
  have different (offset : BitVec 64) (other : offset≠64#64) : table+offset≠table+64#64:=by
    intro same
    exact other ((BitVec.add_right_inj table).mp same)
  refine ⟨image.domain,image.geometry.table,image.aligned,?_,?_,?_⟩
  · have cell:=image.fields (table+0#64,key) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 0#64 (by decide)] using cell
  · have cell:=image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 8#64 (by decide)] using cell
  · have cell:=image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites])
    simpa [New.putField,StoreWord.put,different 32#64 (by decide)] using cell

/-- All original leaf/order/count stores and the final return are finite
straight-line source work, including failed reads and stores. -/
theorem scalar_tail_quiet (code) : QuietClock.Preserves code afterCopy := by
  rw [shapes.2.2.2.2.1,shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2.2.2]
  repeat first | apply QuietClock.declared | apply QuietClock.sequence | apply QuietClock.store | apply QuietClock.returned

def scalarCopyEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : BitVec 64) :=
  bind (bind source "klen" key) "stride" (New.strideWord key)

theorem scalar_after_node_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key pointer : BitVec 64)
    (fields : ScalarFields source table key) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word 1#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterNode).2.clock≤CopyAny.price key.toNat+1 := by
  have lengthRead:=NewNode.field_read source table key 0 fields.domain fields.arena fields.aligned (by decide) (by decide) tableCell
    (by simpa using fields.length)
  rw [shapes.2.1]
  apply ClockCost.declared_current source "klen" _ key _ (CopyAny.price key.toNat+1) lengthRead
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 fields.domain fields.arena fields.aligned (by decide) (by decide) firstTable fields.stride
  rw [shapes.2.2.1]
  apply ClockCost.declared_current first "stride" _ (New.strideWord key) _ (CopyAny.price key.toNat+1) strideRead
  let current:=scalarCopyEntry source key
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other first "stride" "t" (New.strideWord key) (by decide)).trans firstTable
  have currentNode : current.locals.lookup (ofString "n")=some (.val (.word 1#64)):=
    (bind_lookup_other first "stride" "n" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "n" key (by decide)).trans nodeCell)
  have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other first "stride" "key" (New.strideWord key) (by decide)).trans ((bind_lookup_other source "klen" "key" key (by decide)).trans keyCell)
  have currentLength : current.locals.lookup (ofString "klen")=some (.val (.word key)):=
    (bind_lookup_other first "stride" "klen" (New.strideWord key) (by decide)).trans (bind_lookup_same _ _ _)
  have currentStride : current.locals.lookup (ofString "stride")=some (.val (.word (New.strideWord key))):=bind_lookup_same _ _ _
  have keysRead:=NewNode.field_read current table (New.keysPointer table) 32 fields.domain fields.arena fields.aligned (by decide) (by decide) currentTable fields.keys
  have destinationRead : eval current (.op .add [.load .one (NewNode.address 32),.panop .mul [localVar "n",localVar "stride"]])=
      some (.val (.word (New.keysPointer table+New.strideWord key))):=by
    simp only [eval] at keysRead ⊢
    rw [evalHOLExact]
    simp only [evalListHOLExact,keysRead]
    simp [evalHOLExact,evalListHOLExact,localVar,currentNode,currentStride,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) copyArguments=
      some (CopyGeneral.values (New.keysPointer table+New.strideWord key) pointer key.toNat):=by
    have number : BitVec.ofNat 64 key.toNat=key:=by simp [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp only [eval] at destinationRead
    simp only [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,destinationRead]
    simp [evalHOLExact,localVar,currentKey,currentLength,number]
  rw [shapes.2.2.2.1]
  have front:=CopyAny.call_cost current copyArguments (New.keysPointer table+New.strideWord key) pointer key.toNat small args
    (CopyGeneral.original_code current.code installed)
  simpa only [current,scalarCopyEntry,first,Nat.add_zero] using ClockCost.sequence_current current _ afterCopy (CopyAny.price key.toNat+1) 0 front
    (ClockCost.of_quiet current.code afterCopy (scalar_tail_quiet current.code))

/-- All outcomes of the real first leaf construction at its actual scalar
key width. Copy failure and short clocks need no additional success premise. -/
theorem scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+2 := by
  let output:=evaluateHOLFiniteState source body
  have actual : evaluateHOLFiniteState source body=(output.1,output.2):=rfl
  rw [shapes.1] at actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t"]=some [.val (.word table)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell]
  rcases NewNode.scoped_trace source output.2 table 1#64 cap (NewNode.from_scalar_empty image) installed "n" [localVar "t"] afterNode args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    have bound:=stopped.1
    omega
  · obtain ⟨target,inner,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "n" (.val (.word 1#64))
    have fields : ScalarFields current table key:=(ScalarFields.after_next image).of_frame frame
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "n" "t" (.val (.word 1#64)) (by decide)).trans tableCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
      (CallNormal.continuation_lookup_other source target "n" "key" (.val (.word 1#64)) (by decide)).trans keyCell
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    have cost:=scalar_after_node_cost current table key pointer fields (by rw [code]; exact installed)
      currentTable (CallNormal.continuation_lookup_same source target "n" (.val (.word 1#64))) currentKey small
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+1 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+2
    omega

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.from_scalar_empty
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.ScalarFields.after_next
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_tail_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_after_node_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.scalar_empty_cost

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem scalar_empty_finish_quiet (code) : QuietClock.Preserves code emptyFinish := by
  rw [guard_shapes.2.2.1]
  exact QuietClock.sequence code _ _ (QuietClock.store code _ _) (QuietClock.returned code _)

/-- An actual zero leaf takes only the real first-insertion branch. The
callee allowance uses its scalar key width, without a32byte key image. -/
theorem scalar_after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 0#64))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤CopyAny.price key.toNat+3 := by
  have keysRead:=NewNode.field_read source table (New.keysPointer table) 32 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+32#64,New.keysPointer table) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.2.2.1]
  apply ClockCost.declared_current source "keys" _ (New.keysPointer table) _ (CopyAny.price key.toNat+3) keysRead
  let current:=bind source "keys" (New.keysPointer table)
  have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "keys" "t" (New.keysPointer table) (by decide)).trans tableCell
  have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
    (bind_lookup_other source "keys" "key" (New.keysPointer table) (by decide)).trans keyCell
  have currentValue : current.locals.lookup (ofString "value")=some (.val (.word value)):=
    (bind_lookup_other source "keys" "value" (New.keysPointer table) (by decide)).trans valueCell
  have currentLeaf : current.locals.lookup (ofString "leaf")=some (.val (.word 0#64)):=
    (bind_lookup_other source "keys" "leaf" (New.keysPointer table) (by decide)).trans leafCell
  rw [after_keys_empty current currentLeaf,guard_shapes.2.1]
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment current.code.lookup (ofString "htab_new_leaf")
    (ofString "t") (ofString "key") (ofString "value") NewLeaf.body .one table pointer value
    (by decide) (by decide) (by decide) (NewLeaf.original_code current.code installed)
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) leafArguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentTable,currentKey,currentValue]
  have cost:=NewLeaf.scalar_empty_cost (callEntryStateHOLFinite current callee) table key cap pointer (image.of_erase rfl) installed tCell kCell small
  simpa only [current,Nat.add_zero] using ClockCost.scoped_current current (ofString "nl") .one (ofString "htab_new_leaf") leafArguments
    [.val (.word table),.val (.word pointer),.val (.word value)] NewLeaf.body emptyFinish callee .one (CopyAny.price key.toNat+2) 0 args called cost
    (ClockCost.of_quiet current.code emptyFinish (scalar_empty_finish_quiet current.code))

/-- The actual empty scalar lookup returns zero and retains the same table
before the first leaf construction. Every stopped outcome is priced too. -/
theorem scalar_after_stride_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source afterStride).2.clock≤CopyAny.price key.toNat+4 := by
  let output:=evaluateHOLFiniteState source afterStride
  have actual : evaluateHOLFiniteState source afterStride=(output.1,output.2):=rfl
  rw [entry_shapes.2.2.1] at actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "t",localVar "key"]=
      some [.val (.word table),.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tableCell,keyCell]
  rcases FindLeaf.scoped_scalar_empty_trace source output.2 table key cap pointer image installed "leaf" [localVar "t",localVar "key"] afterLeaf args output.1 actual with stopped|reached
  · change source.clock-output.2.clock≤CopyAny.price key.toNat+4
    have bound:=stopped.1
    omega
  · obtain ⟨target,inner,frame,clock,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" (.val (.word 0#64))
    have currentImage : New.ScalarEmpty current table key cap:=image.of_erase frame
    have currentTable : current.locals.lookup (ofString "t")=some (.val (.word table)):=
      (CallNormal.continuation_lookup_other source target "leaf" "t" (.val (.word 0#64)) (by decide)).trans tableCell
    have currentKey : current.locals.lookup (ofString "key")=some (.val (.word pointer)):=
      (CallNormal.continuation_lookup_other source target "leaf" "key" (.val (.word 0#64)) (by decide)).trans keyCell
    have currentValue : current.locals.lookup (ofString "value")=some (.val (.word value)):=
      (CallNormal.continuation_lookup_other source target "leaf" "value" (.val (.word 0#64)) (by decide)).trans valueCell
    have code:=congrArg PanSemStateFiniteExact.code frame
    change current.code=source.code at code
    have cost:=scalar_after_leaf_cost current table key cap pointer value currentImage (by rw [code]; exact installed)
      currentTable currentKey currentValue (CallNormal.continuation_lookup_same source target "leaf" (.val (.word 0#64))) small
    rw [continued] at cost
    change current.clock-inner.clock≤CopyAny.price key.toNat+3 at cost
    have entryClock : current.clock=target.clock:=rfl
    have exitClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤CopyAny.price key.toNat+4
    omega

/-- Whole unchanged htab_set at a genuinely fresh scalar table. The bound
includes both real helper calls and the full variable-length key copy. -/
theorem scalar_empty_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (valueCell : source.locals.lookup (ofString "value")=some (.val (.word value))) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price key.toNat+4 := by
  have lengthRead:=NewNode.field_read source table key 0 image.domain image.geometry.table image.aligned (by decide) (by decide) tableCell
    (image.fields (table+0#64,key) (by simp [New.scalarWrites]))
  rw [entry_shapes.1]
  apply ClockCost.declared_current source "klen" _ key _ (CopyAny.price key.toNat+4) lengthRead
  let first:=bind source "klen" key
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other source "klen" "t" key (by decide)).trans tableCell
  have strideRead:=NewNode.field_read first table (New.strideWord key) 8 image.domain image.geometry.table image.aligned (by decide) (by decide) firstTable
    (image.fields (table+8#64,New.strideWord key) (by simp [New.scalarWrites]))
  rw [entry_shapes.2.1]
  apply ClockCost.declared_current first "stride" _ (New.strideWord key) _ (CopyAny.price key.toNat+4) strideRead
  let current:=bind first "stride" (New.strideWord key)
  have kept (name : String) (notStride : ofString "stride"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (bind_lookup_other first "stride" name (New.strideWord key) notStride).trans (bind_lookup_other source "klen" name key notLength)
  exact scalar_after_stride_cost current table key cap pointer value (image.of_erase rfl) installed
    ((kept "t" (by decide) (by decide)).trans tableCell) ((kept "key" (by decide) (by decide)).trans keyCell)
    ((kept "value" (by decide) (by decide)).trans valueCell) small

/-- Actual ignored first-insertion caller at the scalar constructor's
width. Argument values come from the same evaluated call. -/
theorem scalar_empty_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table key cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) (small : key.toNat+32<2^64) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤CopyAny.price key.toNat+5 := by
  obtain ⟨callee,called,tCell,kCell,vCell⟩:=word_triple_environment source.code.lookup (ofString "htab_set")
    (ofString "t") (ofString "key") (ofString "value") body .one table pointer value
    (by decide) (by decide) (by decide) (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "htab_set") arguments
    [.val (.word table),.val (.word pointer),.val (.word value)] body callee .one (CopyAny.price key.toNat+4) args called
    (scalar_empty_cost (callEntryStateHOLFinite source callee) table key cap pointer value (image.of_erase rfl) installed tCell kCell vCell small)

/-- The real20byte first account-access insertion, including its ordinary
caller and every copy/setup failure or timeout. -/
theorem account_first_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pointer value : BitVec 64)
    (image : New.ScalarEmpty source table 20#64 cap) (installed : OriginalCode.Installed source.code)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word value)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)).2.clock≤29 := by
  simpa [CopyAny.price] using scalar_empty_call_cost source table 20#64 cap pointer value image installed arguments args (by decide)

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_finish_quiet
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_leaf_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_after_stride_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.scalar_empty_call_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.account_first_call_cost
