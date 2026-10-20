import InitECandidate.Solver.Input.BytesVectorPackedCost
import InitECandidate.Solver.Input.HeapReleaseReturn
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.BytesVector
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal packed hash/release restores the saved outer mark after
the real inner list hash restores its own current heap cursor. -/
theorem after_pack_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out mark stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n small arena aligned
  have args := merkle_arguments source cursor out n packed output
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have merkleArena := AllocatedBytes.Arena.weaken _ (832+64*PackBytes.chunks n) (32*max 1 (2*PackBytes.chunks n)) temporaryArena (by omega)
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.2] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterMerkle value (safe.summary_full source).2.1 run
  have nextHeap := Merkle.ignored_return_heap source middle cursor (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n))
    (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out stp accel depth depthSmall (by rw [number]; exact depthBound) (by rw [number]; exact depthBound)
    workspace.sha heap (by rw [number]; exact packedArena) (by rw [number]; exact merkleArena) temporaryAligned merkleArguments args normal
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (summary.1 rfl).trans saved
  have fields := evaluation_fields source middle _ none normal
  exact HeapScope.release_return_heap middle post mark (cursor+BitVec.ofNat 64 (PackBytes.padded n)) (fields.2.2.2.symm ▸ workspace.sha.installed) nextMark nextHeap value remaining

/-- The actual normal scoped pack invocation derives its returned tuple,
normal continuation and saved-caller restoration before applying the real
hash/release suffix. -/
theorem after_mark_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out mark stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n small arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code workspace.sha.installed)
  rw [body_shape.2.2.1] at run
  obtain ⟨funded,target,returned,final,actual,checked,continued,endpoint⟩ := CallNormal.scoped_normal source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n)
    PackBytes.body afterPack callee PackBytes.returnShape args called value run
  have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n small workspace.sha.installed nLocal heap packedArena returned actual
  have calleeWorkspace := SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace
  have nextWorkspace := SszHash.Workspace.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros calleeWorkspace PackBytes.body (some (.returned returned)) actual
    (fun key different=>PackBytes.globals key source.code workspace.sha.installed different)
  let resumed := CallNormal.continuationEntry source target "pk" returned
  have resumedWorkspace := SszHash.Workspace.of_fields target resumed stp accel chunk zeros nextWorkspace rfl rfl (by intro key different; rfl)
  have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
    (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
  have currentN := (CallNormal.continuation_lookup_other source target "pk" "n" returned (by decide)).trans count
  have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
  have currentMark := (CallNormal.continuation_lookup_other source target "pk" "mark" returned (by decide)).trans saved
  have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
    change target.globals.lookup (ofString "heap_ptr")=_
    rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
  have restored := after_pack_return_heap resumed final cursor out mark stp accel chunk zeros n depth small depthSmall depthBound resumedWorkspace pk currentN currentOut currentMark currentHeap arena aligned outArena value continued
  rw [endpoint]
  exact restored

/-- A real short-vector execution is exactly its terminating zero/copy
branch; the allocating hash continuation cannot be reached. -/
theorem short_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat) (short : n≤32)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState source shortBody := by
  have read := test_read source n (by omega) count
  simp only [if_pos short,eval] at read
  rw [body_shape.1,evaluateHOLFiniteState_seq_line780,guard,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
  have never := short_stops source
  generalize observed : evaluateHOLFiniteState source shortBody=response at never ⊢
  obtain ⟨result,post⟩ := response
  cases result with
  | none=>exact (never rfl).elim
  | some result=>rfl

theorem short_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code shortBody :=
  GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one (Zero.original_code code installed) (Zero.globals key code))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "memcpy") copyArguments CopyGeneral.formals Copy32.body .one (CopyGeneral.original_code code installed) (Copy32.globals key code)) (GlobalEffects.returned key code _))

/-- Every actual normal original byte-vector hash restores its entry heap,
including its nonallocating short branch and actual packed Merkle branch. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n depth : Nat)
    (small : n≤134217728) (depthSmall : depth<64) (depthBound : PackBytes.chunks n≤2^depth) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  by_cases short : n≤32
  · rw [short_entry source n short count] at run
    have frame := short_globals (ofString "heap_ptr") source.code workspace.sha.installed source rfl
    rw [run] at frame
    exact (congrArg Prod.snd frame).trans heap
  ·
    rw [long_entry source n small (by omega) count,body_shape.2.1] at run
    obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
      (HeapScope.mark_original_code source.code workspace.sha.installed) (some (.returned value)) run (by simp)
    let entry := bind {source with clock:=source.clock-1} "mark" cursor
    have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
    have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
      bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
    have restored := after_mark_return_heap entry final p cursor out cursor stp accel chunk zeros n depth small depthSmall depthBound nextWorkspace
      ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output) (bind_lookup_same _ _ _) heap arena aligned outArena value remaining
    rw [endpoint]
    exact restored

end InitECandidate.Solver.Input.BytesVector

#print axioms InitECandidate.Solver.Input.BytesVector.after_pack_return_heap
#print axioms InitECandidate.Solver.Input.BytesVector.after_mark_return_heap
#print axioms InitECandidate.Solver.Input.BytesVector.body_return_heap
