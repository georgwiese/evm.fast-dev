import InitECandidate.Solver.Input.PackBytesAllocation
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def packedValue (cursor : BitVec 64) (n : Nat) : ValueHOL 64 := .rStruct [.val (.word cursor),.val (.word (BitVec.ofNat 64 (chunks n)))]

private theorem ignored_locals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key function : MlS) (arguments : List (ExpHOL 64))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : post.locals.lookup key=source.locals.lookup key := by
  have safe : LocalPrefix key (.call (some (none,none)) function arguments) := .call none _ _ (by intro name impossible; cases impossible)
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [run] at summary
  exact summary.1 rfl

private theorem after_copy_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterCopy=(some (.returned value),post)) :
    value=packedValue cursor n ∧ post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") := by
  have safe : LocalPrefix (ofString "buf") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.2] at run
  obtain ⟨cleared,normal,returned⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
  have clearedBuf : cleared.locals.lookup (ofString "buf")=some (.val (.word cursor)) := (ignored_locals source cleared _ _ _ normal).trans buffer
  have clearedCount : cleared.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))) := (ignored_locals source cleared _ _ _ normal).trans count
  have actual : evaluateHOLFiniteState cleared (.return (.rstruct [localVar "buf",localVar "count"]))=(some (.returned (packedValue cursor n)),emptyLocalsHOLFinite cleared) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,toExact,localVar,clearedBuf,clearedCount,packedValue,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have valueEq : value=packedValue cursor n := by
    have h:=congrArg Prod.fst (returned.symm.trans actual)
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using h
  have endpoint : post=emptyLocalsHOLFinite cleared := by
    rw [actual] at returned
    exact (congrArg Prod.snd returned).symm
  have pure : GlobalEffects.Preserves (ofString "heap_ptr") source.code (.call (some (none,none)) (ofString "memzero") zeroArguments) :=
    GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code installed) (Zero.globals (ofString "heap_ptr") source.code)
  have frame := pure source rfl
  rw [normal] at frame
  refine ⟨valueEq,?_⟩
  rw [endpoint]
  exact congrArg Prod.snd frame

private theorem buffer_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterBuffer=(some (.returned value),post)) :
    value=packedValue cursor n ∧ post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") := by
  have safe : LocalPrefix (ofString "buf") (.call (some (none,none)) (ofString "memcpy") copyArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at run
  obtain ⟨copied,normal,remaining⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
  have fields := evaluation_fields source copied _ none normal
  have copiedBuf : copied.locals.lookup (ofString "buf")=some (.val (.word cursor)) := (ignored_locals source copied _ _ _ normal).trans buffer
  have copiedCount : copied.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 (chunks n)))) := (ignored_locals source copied _ _ _ normal).trans count
  have result := after_copy_return copied post cursor n (fields.2.2.2.symm ▸ installed) copiedBuf copiedCount value remaining
  have pure : GlobalEffects.Preserves (ofString "heap_ptr") source.code (.call (some (none,none)) (ofString "memcpy") copyArguments) :=
    GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (ofString "memcpy") copyArguments CopyGeneral.formals Copy32.body .one
      (CopyGeneral.original_code source.code installed) (Copy32.globals (ofString "heap_ptr") source.code)
  have frame := pure source rfl
  rw [normal] at frame
  exact ⟨result.1,result.2.trans (congrArg Prod.snd frame)⟩

/-- The original actual normal pack return derives its exact allocated
buffer/count tuple and allocator heap update. No future return is assumed. -/
theorem body_return_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (arena : AllocatedBytes.Arena cursor (padded n))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=packedValue cursor n ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))))) := by
  obtain ⟨paid,final,remaining,endpoint⟩ := allocation_prefix source post cursor n small count installed heap arena (some (.returned value)) run (by simp)
  let entry := buffered source cursor n
  have fields := buffered_fields source cursor n
  have result := buffer_return entry final cursor n installed fields.1 fields.2.1 value remaining
  refine ⟨result.1,?_⟩
  rw [endpoint]
  change final.globals.lookup (ofString "heap_ptr")=_
  rw [result.2]
  change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n)))))).lookup _=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem rounded_padded (cursor : BitVec 64) (n : Nat) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0) :
    PersistentAlloc.rounded cursor (BitVec.ofNat 64 (padded n))=cursor+BitVec.ofNat 64 (padded n) := by
  have upper := arena.upper
  have number : (BitVec.ofNat 64 (padded n)).toNat=padded n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have multiple : padded n%8=0 := by have h:=(padding_bounds n).2.2.1; omega
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat cursor (BitVec.ofNat 64 (padded n)) (by rw [number]; omega),BitVec.toNat_add_of_lt (by rw [number]; omega),number]
  omega

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.body_return_data
#print axioms InitECandidate.Solver.Input.PackBytes.rounded_padded
