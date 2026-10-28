import InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory
import InitECandidate.Solver.Input.CurrentHash.MerkleBodyCost
import InitECandidate.Solver.Input.CurrentHash.MemoryGlobals

namespace InitECandidate.Solver.Input.CurrentHash.MerkleMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Physical facts at this actual call. Numerical cursor bounds are the real
persistent heap bounds; zero hashes are only read by the empty-tree branch. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros query : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  domain : source.memaddrs=InitE.ordinaryDomain
  zeroCell : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))
  zeroArena : AllocatedBytes.Arena zeros 2048
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))
  heapLower : 2701131776≤cursor.toNat
  heapBound : cursor.toNat≤2952790016
  aligned : cursor.toNat%8=0
  below : query.toNat<cursor.toNat

theorem Context.of_frozen {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor zeros query : BitVec 64}
    (data : Context source cursor zeros query) (frame : CeilLog2.frozen target=CeilLog2.frozen source) : Context target cursor zeros query := by
  have code := congrArg PanSemStateFiniteExact.code frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  refine ⟨?_,domain.trans data.domain,?_,data.zeroArena,?_,data.heapLower,data.heapBound,data.aligned,data.below⟩
  · rw [code]; exact data.installed
  · rw [globals]; exact data.zeroCell
  · rw [globals]; exact data.heap

theorem Context.at_callee {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor zeros query : BitVec 64}
    (data : Context source cursor zeros query) (callee : HolFiniteMapExact MlS (ValueHOL 64)) : Context (callEntryStateHOLFinite source callee) cursor zeros query :=
  ⟨data.installed,data.domain,data.zeroCell,data.zeroArena,data.heap,data.heapLower,data.heapBound,data.aligned,data.below⟩

theorem empty_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros out query : BitVec 64) (target : Nat)
    (context : Context source cursor zeros query) (small : target<64)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (maximum : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source MerkleBodyCost.zeroBody=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) MerkleBodyCost.zeroArguments =
      some (CopyGeneral.values out (zeros+BitVec.ofNat 64 (32*target)) 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,MerkleBodyCost.zeroArguments,localVar,output,maximum,context.zeroCell,
      CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have table := AllocatedBytes.Arena.subrange zeros 2048 (32*target) 32 context.zeroArena (by omega)
  have memory := MemoryAt.copy_returned source post MerkleBodyCost.zeroArguments (zeros+BitVec.ofNat 64 (32*target)) out query 32
    context.installed context.domain args table outArena outAway value actual
  have globals : GlobalEffects.Preserves (ofString "heap_ptr") source.code MerkleBodyCost.zeroBody :=
    GlobalEffects.sequence _ _ _ _ (MemoryGlobals.call .copy _ source.code context.installed (some none) _) (GlobalEffects.returned _ _ _)
  have frame := globals source rfl
  rw [actual] at frame
  exact ⟨memory,(congrArg Prod.snd frame).trans context.heap⟩

theorem after_depth_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor zeros out query : BitVec 64) (n depth target budget : Nat)
    (context : Context source cursor zeros query) (data : MerkleAllocationCost.Params source p n depth target)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (budgetSmall : budget<58) (depthBound : depth≤budget) (targetBound : target≤budget) (depths : depth≤target) (ceiling : n≤2^depth)
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source Merkle.afterDepth=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have upper : 2^depth≤2^57 := Nat.pow_le_pow_right (by decide) (by omega)
  by_cases empty : n=0
  · have count : source.locals.lookup (ofString "n")=some (.val (.word 0#64)) := by simpa [empty] using data.count
    have stops := (show NoFallthrough MerkleBodyCost.zeroBody from .sequence _ _ (.returned _)) source
    rw [MerkleBodyCost.source_shape.2,evaluateHOLFiniteState_seq_line780,MerkleBodyCost.zero_guard source 0#64 count,if_pos rfl] at actual
    generalize computed : evaluateHOLFiniteState source MerkleBodyCost.zeroBody=observed at actual stops
    obtain ⟨result,targetState⟩ := observed
    cases result with
    | none => exact False.elim (stops rfl)
    | some result => exact empty_memory source post cursor zeros out query target context (by omega) output data.maximum outArena outAway value (computed.trans actual)
  · have number : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nonzero : BitVec.ofNat 64 n≠0#64 := by
      intro zero
      have equal := congrArg BitVec.toNat zero
      rw [number] at equal
      exact empty equal
    have skipped : evaluateHOLFiniteState source MerkleBodyCost.zeroGuard=(none,source) := by
      rw [MerkleBodyCost.zero_guard source (BitVec.ofNat 64 n) data.count,if_neg nonzero]
    rw [MerkleBodyCost.source_shape.2,StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)] at actual
    exact MerkleAllocationMemory.memory source post p cursor out query n depth target data context.installed context.domain output
      (by omega) ceiling (by omega) (by omega) depths context.heap context.heapLower context.heapBound context.aligned
      inputArena outArena context.below outAway value actual

/-- Complete actual Merkle body: real logarithm/max prefix, empty branch and
actual marked allocation/fill/tree/release. Metadata and the entering heap are
retained on the same normal return; allocation room is derived from that run. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p n limit out cursor zeros query : BitVec 64) (budget : Nat)
    (context : Context source cursor zeros query) (small : budget<58) (countBound : n.toNat≤2^budget) (limitBound : limit.toNat≤2^budget)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (maximum : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (Code.body .merkleize)=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [MerkleBodyCost.source_shape.1] at actual
  obtain ⟨current,final,dl,dn,restoration,dlBound,dnBound,limitPower,countPower,dlPrevious,dnPrevious,sizeBound,
    locals,paid,clock,prefixCost,frame,remaining,endpoint,restored⟩ :=
    Merkle.depth_prefix source post n limit budget (by omega) countBound limitBound context.installed count maximum
      (some (.returned value)) actual (by simp)
  have kept (name : String) (notDl : ofString "dl"≠ofString name) (notDn : ofString "dn"≠ofString name)
      (notTarget : ofString "target"≠ofString name) : current.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,notDl,notDn,notTarget]
  have currentCount : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n.toNat))) := by
    simpa using (kept "n" (by decide) (by decide) (by decide)).trans count
  have currentDepth : current.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "target"≠ofString "dn" from by decide]
  have currentTarget : current.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 (max dl dn)))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have data : MerkleAllocationCost.Params current p n.toNat dn (max dl dn) :=
    ⟨(kept "p" (by decide) (by decide) (by decide)).trans pointer,currentCount,currentDepth,currentTarget⟩
  have image := after_depth_memory current final p cursor zeros out query n.toNat dn (max dl dn) budget (context.of_frozen frame) data
    ((kept "out" (by decide) (by decide) (by decide)).trans output) small dnBound (Nat.max_le.mpr ⟨dlBound,dnBound⟩)
    (Nat.le_max_right _ _) countPower inputArena outArena outAway value remaining
  have prefixMemory := congrArg PanSemStateFiniteExact.memory frame
  change current.memory=source.memory at prefixMemory
  have finalMemory : post.memory=final.memory := by
    rw [endpoint]
    have same := congrArg PanSemStateFiniteExact.memory (restored final)
    exact same
  have finalGlobals : post.globals=final.globals := by
    rw [endpoint]
    have same := congrArg PanSemStateFiniteExact.globals (restored final)
    exact same
  exact ⟨(congrArg (fun memory => memory query) finalMemory).trans (image.1.trans (congrArg (fun memory => memory query) prefixMemory)),
    (congrArg (fun globals => globals.lookup (ofString "heap_ptr")) finalGlobals).trans image.2⟩

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p n limit out cursor zeros query : BitVec 64) (budget : Nat)
    (context : Context source cursor zeros query) (small : budget<58) (countBound : n.toNat≤2^budget) (limitBound : limit.toNat≤2^budget)
    (inputArena : AllocatedBytes.Arena p (32*n.toNat)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Merkle.values p n limit out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  obtain ⟨callee,called,pointer,count,maximum,output⟩ := Merkle.environment source.code.lookup p n limit out (Merkle.original_code source.code context.installed)
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "merkleize") arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_memory (callEntryStateHOLFinite source callee) target p n limit out cursor zeros query budget
    (context.at_callee callee) small countBound limitBound pointer count maximum output inputArena outArena outAway value bodyRun
  rw [endpoint]
  exact image

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p n limit out cursor zeros query : BitVec 64) (budget : Nat)
    (context : Context source cursor zeros query) (small : budget<58) (countBound : n.toNat≤2^budget) (limitBound : limit.toNat≤2^budget)
    (inputArena : AllocatedBytes.Arena p (32*n.toNat)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Merkle.values p n limit out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(none,post)) :
    post.memory query=source.memory query :=
  (call_frame source post p n limit out cursor zeros query budget context small countBound limitBound inputArena outArena outAway arguments args actual).1

end InitECandidate.Solver.Input.CurrentHash.MerkleMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.Context.of_frozen
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.Context.at_callee
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.empty_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.after_depth_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.body_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.call_memory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.call_frame
