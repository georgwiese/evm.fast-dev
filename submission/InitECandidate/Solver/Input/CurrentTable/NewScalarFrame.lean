import InitECandidate.Solver.Input.CurrentTable.NewScalarArrays
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def strideWord (key : BitVec 64) : BitVec 64:=(key+7#64)&&&(0#64-8#64)
def scalarFieldsEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64):=
  bind (bind (tableEntry source heap) "stride" (strideWord key)) "ncap" cap

def scalarHeaderStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap stride : BitVec 64):=
  putField (putField (putField (putField source table 0 key) table 8 stride) table 16 cap) table 24 0#64

/-- The unchanged stride and minimum-capacity prefix at arbitrary key width. -/
theorem scalar_prefix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key cap : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat) :
    evaluateHOLFiniteState source afterTable=
      let ready:=bind (bind source "stride" (strideWord key)) "ncap" cap
      let output:=evaluateHOLFiniteState ready fields
      (output.1,restore source "stride" (restore (bind source "stride" (strideWord key)) "ncap" output.2)) := by
  have strideRead : eval source strideExpression=some (.val (.word (strideWord key))) := by
    simp [strideExpression,strideWord,eval,evalHOLExact,evalListHOLExact,toExact,localVar,keyCell,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and]
  let first:=bind source "stride" (strideWord key)
  have capRead : eval first (localVar "cap")=some (.val (.word cap)) := by
    have kept:=(bind_lookup_other source "stride" "cap" (strideWord key) (by decide)).trans capCell
    change eval (bind source "stride" (strideWord key)) (localVar "cap")=_
    simp [eval,evalHOLExact,toExact,localVar,kept]
  let ready:=bind first "ncap" cap
  have ncapCell : ready.locals.lookup (ofString "ncap")=some (.val (.word cap)):=bind_lookup_same _ _ _
  have guardRun : evaluateHOLFiniteState ready capacityGuard=(none,ready) := by
    simp [capacityGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,localVar,ncapCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,show ¬cap.toNat<2 from by omega]
  have afterRun : evaluateHOLFiniteState ready afterNcap=evaluateHOLFiniteState ready fields := by
    rw [shapes.2.2.2,evaluateHOLFiniteState_seq_line780,guardRun]
  let output:=evaluateHOLFiniteState ready fields
  have innerRun : evaluateHOLFiniteState ready afterNcap=(output.1,output.2):=afterRun
  have firstRun : evaluateHOLFiniteState first afterStride=(output.1,restore first "ncap" output.2) := by
    rw [shapes.2.2.1]
    exact ScalarScope.declare_execute first output.2 "ncap" (localVar "cap") cap afterNcap output.1 capRead innerRun
  rw [shapes.2.1]
  exact ScalarScope.declare_execute source (restore first "ncap" output.2) "stride" strideExpression (strideWord key) afterStride output.1 strideRead firstRun

/-- Exactly the four initial header stores with their actual arbitrary key
width/stride. The array-allocation continuation stays the original one. -/
theorem scalar_fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key cap stride : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (strideCell : source.locals.lookup (ofString "stride")=some (.val (.word stride)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) :
    evaluateHOLFiniteState source fields=evaluateHOLFiniteState (scalarHeaderStored source table key cap stride) keysCall := by
  let first:=putField source table 0 key
  let second:=putField first table 8 stride
  let third:=putField second table 16 cap
  have one:=store_field source table key 0 (localVar "key_len") domain arena aligned (by decide) (by decide) tableCell (Request.local_word source "key_len" key keyCell)
  have two:=store_field first table stride 8 (localVar "stride") domain arena aligned (by decide) (by decide) tableCell (Request.local_word first "stride" stride strideCell)
  have three:=store_field second table cap 16 (localVar "cap") domain arena aligned (by decide) (by decide) tableCell (Request.local_word second "cap" cap capCell)
  have four:=store_field third table 0#64 24 (.const 0#64) domain arena aligned (by decide) (by decide) tableCell rfl
  rw [fields_shape,evaluateHOLFiniteState_seq_line780,one]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,three]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,four]
  rfl

/-- Whole current constructor normal frame for any scalar key width and
capacity at least two. All four actual allocations supply their own room;
no initialized array contents or substituted table implementation is used. -/
theorem body_scalar_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key cap : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word key)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) (atLeastTwo : 2≤cap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word heap) ∧ AllocatedBytes.Arena heap 88 ∧ PersistentNormalFrame source post heap := by
  rw [shapes.1] at normal
  rcases CurrentAlloc.scoped_classified source post "t" [.const 88#64] afterTable heap 88#64 rfl arena.code heapCell heapBound _ normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨funded,room,middle,continued,endpoint⟩:=reached
    have tableArena : AllocatedBytes.Arena heap 88:=⟨heapArena.lower,by change heap.toNat+88≤2952790016 at room; omega⟩
    change evaluateHOLFiniteState (tableEntry source heap) afterTable=(some (.returned value),middle) at continued
    have currentKey : (tableEntry source heap).locals.lookup (ofString "key_len")=some (.val (.word key)):=
      (bind_lookup_other _ "t" "key_len" heap (by decide)).trans keyCell
    have currentCap : (tableEntry source heap).locals.lookup (ofString "cap")=some (.val (.word cap)):=
      (bind_lookup_other _ "t" "cap" heap (by decide)).trans capCell
    rw [scalar_prefix_execute (tableEntry source heap) key cap currentKey currentCap atLeastTwo] at continued
    let entered:=scalarFieldsEntry source heap key cap
    let inner:=(evaluateHOLFiniteState entered fields).2
    have observed:=congrArg Prod.fst continued
    have restored:=congrArg Prod.snd continued
    dsimp only at restored
    change (evaluateHOLFiniteState entered fields).1=some (.returned value) at observed
    have fieldsRun : evaluateHOLFiniteState entered fields=(some (.returned value),inner):=Prod.ext observed rfl
    have tableLocal : entered.locals.lookup (ofString "t")=some (.val (.word heap)) :=
      (bind_lookup_other _ "ncap" "t" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "t" (strideWord key) (by decide)).trans (bind_lookup_same _ _ _))
    have keyLocal : entered.locals.lookup (ofString "key_len")=some (.val (.word key)) :=
      (bind_lookup_other _ "ncap" "key_len" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "key_len" (strideWord key) (by decide)).trans currentKey)
    have strideLocal : entered.locals.lookup (ofString "stride")=some (.val (.word (strideWord key))) :=
      (bind_lookup_other _ "ncap" "stride" cap (by decide)).trans (bind_lookup_same _ _ _)
    have capLocal : entered.locals.lookup (ofString "cap")=some (.val (.word cap)) :=
      (bind_lookup_other _ "ncap" "cap" cap (by decide)).trans
        ((bind_lookup_other _ "stride" "cap" (strideWord key) (by decide)).trans currentCap)
    have ncapLocal : entered.locals.lookup (ofString "ncap")=some (.val (.word cap)):=bind_lookup_same _ _ _
    rw [scalar_fields_execute entered heap key cap (strideWord key) arena.domain tableArena heapAligned tableLocal keyLocal strideLocal capLocal] at fieldsRun
    let ready:=scalarHeaderStored entered heap key cap (strideWord key)
    let next:=PersistentAlloc.rounded heap 88#64
    have checked:=PersistentAlloc.guards heap 88#64 room
    have nextArena : AllocatedBytes.Arena next 0:=
      ⟨by have low:=heapArena.lower; have grows:=checked.2.2.1; change heap.toNat+88≤next.toNat at grows; omega,
        by have upper:=checked.2.2.2.1; change next.toNat≤2952790016 at upper; omega⟩
    have nextCell : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) := by
      simp [ready,scalarHeaderStored,putField,entered,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,next]
    have first : PersistentNormalFrame source ready heap := by
      refine ⟨⟨next,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,by have grows:=checked.2.2.1; change heap.toNat+88≤next.toNat at grows; omega⟩,rfl,?_,?_⟩
      · intro name other
        simp [ready,scalarHeaderStored,putField,entered,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
      · intro query before
        have away (offset : Nat) (inside : offset<88) : query≠heap+BitVec.ofNat 64 offset := by
          have number:=byteAddress_toNat heap offset (by omega)
          change (heap+BitVec.ofNat 64 offset).toNat=heap.toNat+offset at number
          intro same
          have equal:=congrArg BitVec.toNat same
          rw [number] at equal
          omega
        change (scalarHeaderStored entered heap key cap (strideWord key)).memory query=source.memory query
        have zeroAway : query≠heap:=by intro same; subst query; omega
        simp [scalarHeaderStored,putField,StoreWord.put,zeroAway,away 8 (by decide),away 16 (by decide),away 24 (by decide),entered,scalarFieldsEntry,tableEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post]
    have context : ScalarContext ready heap next cap (strideWord key):=
      ⟨first.current_arena arena,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,tableArena,heapAligned,
        by have grows:=checked.2.2.1; change heap.toNat+88≤next.toNat at grows; omega,tableLocal,ncapLocal,strideLocal⟩
    obtain ⟨valueEq,last⟩:=scalar_arrays_frame cap (strideWord key) ready inner heap next context value fieldsRun
    have total:=first.trans source ready inner heap heap last (Nat.le_refl _)
    have physical : LocalEffects.erase post=LocalEffects.erase inner := by
      rw [endpoint,←restored]
      rfl
    exact ⟨valueEq,tableArena,total.of_erase source inner source post heap rfl physical⟩

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_prefix_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.New.scalar_fields_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.New.body_scalar_normal_frame
