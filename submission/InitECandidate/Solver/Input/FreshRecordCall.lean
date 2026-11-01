import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.CurrentAllocationTrace
import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.ClockPaddingFull
import InitECandidate.Solver.Input.FreshRecord
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.FreshRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {F : Type}

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (kind : Kind)
    (known : table (ofString (functionName kind)) = some ([], body kind, .one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString (functionName kind)) [] = some (body kind, callee, .one) := by
  have raw : lookupCodeHOLExact table (ofString (functionName kind)) [] = some (body kind, fun _ => none, .one) := by
    simp [lookupCodeHOLExact, known]
  obtain ⟨callee, called, locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table
    (ofString (functionName kind)) [] (body kind) (fun _ => none) .one raw
  exact ⟨callee, called⟩

/-- Actual te_new/msg_new caller. Each initializes its complete allocation to
zero and consumes10source clocks including the outer call. -/
theorem call_execute (source : PanSemStateFiniteExact 64 F) (kind : Kind)
    (name : String) (continuation : ProgHOL 64) (pointer : BitVec 64)
    (known : source.code.lookup (ofString (functionName kind)) = some ([], body kind, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (code : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (aligned : pointer.toNat % 8 = 0) (room : pointer.toNat + size kind ≤ 2952790016)
    (mapped : ∀ offset, offset + 8 ≤ size kind → offset % 8 = 0 → source.memaddrs (WitnessRadix.byteAddress pointer offset))
    (enough : 10 ≤ source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName kind)) [] continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind
        {WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind)) with
          memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
          clock := source.clock - 10} name pointer) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called⟩ := environment source.code.lookup kind known
  let entry := callEntryStateHOLFinite source callee
  have bodyRun := execute entry kind pointer heap code zeroCode aligned room mapped (by change 9 ≤ source.clock - 1; omega)
  have frame := canonical entry kind pointer
  have actual := Input.CallNormal.return_execute source (closed entry kind pointer) name .one (ofString (functionName kind)) [] []
    (body kind) continuation callee .one (.val (.word pointer)) rfl called (by omega) bodyRun
    (by simp [shapeOfHOLExact, shapeEqHOL])
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  have clocks : source.clock - 1 - 9 = source.clock - 10 := by omega
  have restored : {closed entry kind pointer with locals := source.locals} =
      {WitnessRadix.PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind)) with
        memory := WitnessRadix.Zero.finalMemory source.memory pointer (size kind)
        clock := source.clock - 10} := by
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, WitnessRadix.PersistentAlloc.post, clocks] using callerFrame
  have nextEq := congrArg (fun state : PanSemStateFiniteExact 64 F =>
    setVarHOLFinite (ofString name) (.val (.word pointer)) state) restored
  change Input.CallNormal.continuationEntry source (closed entry kind pointer) name (.val (.word pointer)) = _ at nextEq
  rw [nextEq] at actual
  exact actual

/-- Exact heap extent, with no alignment padding for these two actual sizes. -/
theorem heap_geometry (kind : Kind) (pointer : BitVec 64) (aligned : pointer.toNat % 8 = 0)
    (room : pointer.toNat + size kind ≤ 2952790016) :
    (WitnessRadix.PersistentAlloc.rounded pointer (BitVec.ofNat 64 (size kind))).toNat = pointer.toNat + size kind := by
  have amount : (BitVec.ofNat 64 (size kind)).toNat = size kind := by cases kind <;> decide
  have multiple : size kind % 8 = 0 := by cases kind <;> decide
  have number := WitnessRadix.PersistentAlloc.rounded_nat pointer (BitVec.ofNat 64 (size kind)) (by rw [amount]; omega)
  rw [number, amount]
  omega

/-- The complete persistent-record clear preserves both earlier allocations
and all later heap locations. -/
theorem memory_outside (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer query : BitVec 64)
    (room : pointer.toNat + size kind ≤ 2952790016)
    (outside : query.toNat < pointer.toNat ∨ pointer.toNat + size kind ≤ query.toNat) :
    (closed source kind pointer).memory query = source.memory query := by
  apply memory_away
  intro offset inside same
  have number := WitnessRadix.byteAddress_toNat pointer offset (by omega)
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  rcases outside with below | high <;> omega

end InitECandidate.Solver.Input.FreshRecord

#print axioms InitECandidate.Solver.Input.FreshRecord.environment
#print axioms InitECandidate.Solver.Input.FreshRecord.call_execute
#print axioms InitECandidate.Solver.Input.FreshRecord.heap_geometry
#print axioms InitECandidate.Solver.Input.FreshRecord.memory_outside


namespace InitECandidate.Solver.Input.FreshRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Catalogue entries for the unchanged current TE/message constructors. -/
theorem original_code (code) (installed : OriginalCode.Installed code) (kind : Kind) :
    code.lookup (ofString (functionName kind))=some ([],body kind,.one) := by
  cases kind with
  | transaction=>
    have checked:=OriginalCode.indexed code installed 793 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_te_new) (by rfl)
    simpa only [functionName,body,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_te_new,
      shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  | message=>
    have checked:=OriginalCode.indexed code installed 421 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_msg_new) (by rfl)
    simpa only [functionName,body,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_msg_new,
      shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Normal execution of the real allocator derives the request room used
by this same constructor, independently of future zeroing or setup success. -/
theorem normal_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),post)) : pointer.toNat+size kind≤2952790016 := by
  rw [body_shape] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const (BitVec.ofNat 64 (size kind))]=
      some (PersistentAlloc.values (BitVec.ofNat 64 (size kind))):=rfl
  rcases CurrentAlloc.scoped_classified source post (localName kind) [.const (BitVec.ofNat 64 (size kind))] (finish kind) pointer (BitVec.ofNat 64 (size kind))
    args installed heap bounded (some (.returned value)) normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · have amount : (BitVec.ofNat 64 (size kind)).toNat=size kind:=by cases kind <;> decide
    simpa only [amount] using reached.2.1

/-- Both actual constructors take at most9body source ticks on every
outcome. Invalid allocation room stops at the real allocator; valid room
supplies the mapped zeroing geometry, without a future-success premise. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (arena : AllocatedBytes.Arena pointer 0) (bounded : pointer.toNat≤2952790016) (aligned : pointer.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) : source.clock-(evaluateHOLFiniteState source (body kind)).2.clock≤9 := by
  by_cases enough : 9≤source.clock
  · by_cases room : pointer.toNat+size kind≤2952790016
    · have owned : AllocatedBytes.Arena pointer (size kind):=⟨arena.lower,by omega⟩
      have mapped : ∀ offset,offset+8≤size kind → offset%8=0 → source.memaddrs (byteAddress pointer offset):=by
        intro offset inside offsetAligned
        exact AllocatedBytes.word_mapped source pointer (size kind) offset domain owned (by omega) aligned offsetAligned
      rw [execute source kind pointer heap (PersistentAlloc.original_code source.code installed) (Zero.original_code source.code installed) aligned room mapped enough]
      change source.clock-(source.clock-9)≤9
      omega
    · generalize actual : evaluateHOLFiniteState source (body kind)=output
      obtain ⟨outcome,post⟩:=output
      change source.clock-post.clock≤9
      rw [body_shape] at actual
      rcases CurrentAlloc.scoped_classified source post (localName kind) [.const (BitVec.ofNat 64 (size kind))] (finish kind) pointer (BitVec.ofNat 64 (size kind))
        rfl installed heap bounded outcome actual with stopped|reached
      · omega
      · have amount : (BitVec.ofNat 64 (size kind)).toNat=size kind:=by cases kind <;> decide
        exact (room (by simpa only [amount] using reached.2.1)).elim
  · have cost:=Nat.sub_le source.clock (evaluateHOLFiniteState source (body kind)).2.clock
    omega

theorem closed_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) :
    (closed source kind pointer).clock=source.clock-9 := rfl

theorem closed_padding {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : Kind) (pointer : BitVec 64) (extra : Nat) :
    closed {source with clock:=source.clock+extra} kind pointer={closed source kind pointer with clock:=source.clock+extra-9} := rfl

/-- A genuine normal constructor supplies its actual room, exact returned
pointer, funding and full post-state. No request room is assumed at entry. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (arena : AllocatedBytes.Arena pointer 0) (bounded : pointer.toNat≤2952790016) (aligned : pointer.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),post)) :
    pointer.toNat+size kind≤2952790016 ∧ 9≤source.clock ∧ value=.val (.word pointer) ∧ post=closed source kind pointer := by
  have room:=normal_room source post kind pointer installed heap bounded value normal
  have owned : AllocatedBytes.Arena pointer (size kind):=⟨arena.lower,by omega⟩
  have mapped : ∀ offset,offset+8≤size kind → offset%8=0 → source.memaddrs (byteAddress pointer offset):=by
    intro offset inside offsetAligned
    exact AllocatedBytes.word_mapped source pointer (size kind) offset domain owned (by omega) aligned offsetAligned
  have actual:=execute {source with clock:=source.clock+9} kind pointer heap (PersistentAlloc.original_code source.code installed)
    (Zero.original_code source.code installed) aligned room mapped (by change 9≤source.clock+9; omega)
  have lifted:=panPropsEvaluateAddClockEq (body kind) source (some (.returned value)) post 9
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq:=congrArg Prod.fst (lifted.symm.trans actual)
  have postEq:=congrArg Prod.snd (lifted.symm.trans actual)
  change {post with clock:=post.clock+9}=closed {source with clock:=source.clock+9} kind pointer at postEq
  rw [closed_padding] at postEq
  obtain ⟨funded,last⟩:=InitECandidate.Solver.strip_full_clock_padding source post (closed source kind pointer) 9 9 (by omega) postEq
  have number:=closed_clock source kind pointer
  rw [←number] at last
  exact ⟨room,funded,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,last⟩

/-- The complete allocated/zeroed record is physically owned and retains
all earlier allocations through the real persistent normal frame. -/
theorem body_normal_complete (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (arena : AllocatedBytes.Arena pointer 0) (bounded : pointer.toNat≤2952790016) (aligned : pointer.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),post)) :
    value=.val (.word pointer) ∧ AllocatedBytes.Arena pointer (size kind) ∧ PersistentNormalFrame source post pointer ∧
      NormalHeapEffects.AtLeast (pointer.toNat+size kind) post ∧ (∀ slot,8*(slot+1)≤size kind → post.memory (pointer+BitVec.ofNat 64 (8*slot))=.word 0#64) := by
  obtain ⟨room,funded,answer,actual⟩:=body_normal source post kind pointer installed heap arena bounded aligned domain value normal
  have amount : (BitVec.ofNat 64 (size kind)).toNat=size kind:=by cases kind <;> decide
  have allocated:=PersistentAlloc.post_persistent_frame source pointer (BitVec.ofNat 64 (size kind)) arena (by rw [amount]; exact room)
  have globals : post.globals=(PersistentAlloc.post source pointer (BitVec.ofNat 64 (size kind))).globals:=by rw [actual]; rfl
  obtain ⟨next,cell,owned,upper,nextAligned,grows⟩:=allocated.nextHeap
  refine ⟨answer,⟨arena.lower,by omega⟩,⟨⟨next,by rw [globals]; exact cell,owned,upper,nextAligned,grows⟩,?_,?_,?_⟩,?_,?_⟩
  · rw [actual]
    rfl
  · intro name other
    rw [globals]
    exact allocated.globals name other
  · intro query before
    rw [actual]
    exact memory_outside source kind pointer query room (Or.inl before)
  · have geometry:=heap_geometry kind pointer aligned room
    have nextCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded pointer (BitVec.ofNat 64 (size kind))))):=by
      rw [globals]
      simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    exact ⟨_,nextCell,by rw [geometry],by rw [geometry]; exact room,
      (PersistentAlloc.guards pointer (BitVec.ofNat 64 (size kind)) (by rw [amount]; exact room)).2.2.2.2⟩
  · intro slot inside
    rw [actual]
    exact zero_cell source kind pointer slot inside

end InitECandidate.Solver.Input.FreshRecord

#print axioms InitECandidate.Solver.Input.FreshRecord.original_code
#print axioms InitECandidate.Solver.Input.FreshRecord.normal_room
#print axioms InitECandidate.Solver.Input.FreshRecord.body_cost
#print axioms InitECandidate.Solver.Input.FreshRecord.closed_clock
#print axioms InitECandidate.Solver.Input.FreshRecord.closed_padding
#print axioms InitECandidate.Solver.Input.FreshRecord.body_normal
#print axioms InitECandidate.Solver.Input.FreshRecord.body_normal_complete


namespace InitECandidate.Solver.Input.FreshRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real constructor caller either stops within10ticks or supplies its
fresh zeroed record, actual persistent frame and heap beyond that record. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (arena : AllocatedBytes.Arena pointer 0) (bounded : pointer.toNat≤2952790016) (aligned : pointer.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (name : String) (continuation : ProgHOL 64)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString (functionName kind)) [] continuation)=(outcome,post)) :
    (source.clock-post.clock≤10 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,current.locals=source.locals.update (ofString name,.val (.word pointer)) ∧
        AllocatedBytes.Arena pointer (size kind) ∧ PersistentNormalFrame source current pointer ∧
        NormalHeapEffects.AtLeast (pointer.toNat+size kind) current ∧
        (∀ slot,8*(slot+1)≤size kind → current.memory (pointer+BitVec.ofNat 64 (8*slot))=.word 0#64) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤10 ∧
        evaluateHOLFiniteState current continuation=(outcome,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called⟩:=environment source.code.lookup kind (original_code source.code installed kind)
  rcases CallNormal.scoped_classified source post name .one (ofString (functionName kind)) [] [] (body kind) continuation callee .one 9 rfl called
    (body_cost (callEntryStateHOLFinite source callee) kind pointer installed heap arena bounded aligned domain) outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,normal,checked,forward,price,continued,endpoint⟩:=reached
    obtain ⟨answer,owned,frame,extent,zeros⟩:=body_normal_complete (callEntryStateHOLFinite source callee) target kind pointer
      installed heap arena bounded aligned domain value normal
    rw [answer] at continued
    let current:=CallNormal.continuationEntry source target name (.val (.word pointer))
    have actualFrame : PersistentNormalFrame source current pointer:=frame.of_erase _ _ source current pointer rfl rfl
    exact Or.inr ⟨current,inner,rfl,owned,actualFrame,extent,zeros,forward,price,continued,endpoint⟩

end InitECandidate.Solver.Input.FreshRecord

#print axioms InitECandidate.Solver.Input.FreshRecord.scoped_trace
