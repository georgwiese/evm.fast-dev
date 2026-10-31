import InitECandidate.Solver.Mpt.NodeRlpFinishScanCost
import InitECandidate.Solver.Mpt.TrieGraphRegions
import InitECandidate.Solver.Input.ScopedCallNoneData
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scan_body_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code scanBody := by
  rw [scan_shapes.2.1]
  exact Input.LocalEffects.scoped_body code (ofString "rl2") .one (ofString "node_ref_len") childArguments (.seq addLength advance)
    NodeRefLen.formals NodeRefLen.body .one (NodeRefLen.original_code code installed) (NodeRefLen.readonly code installed)
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _))

/-- A real scan iteration derives its <=33-byte addition from the actual
reference helper, then performs the genuine payload and counter updates. -/
theorem scan_iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (normal : evaluateHOLFiniteState source scanBody=(none,target)) :
    ∃ added : BitVec 64,added.toNat≤33 ∧ target.locals.lookup (ofString "i")=some (.val (.word (index+1#64))) ∧
      target.locals.lookup (ofString "payload")=some (.val (.word (payload+added))) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have shaped:=normal
  rw [scan_shapes.2.1] at shaped
  obtain ⟨funded,values,body,callee,shape,childTarget,returned,inner,args,called,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none_data source target "rl2" .one (ofString "node_ref_len") childArguments (.seq addLength advance) shaped
  let current:=Input.CallNormal.continuationEntry source childTarget "rl2" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "rl2") .one (ofString "node_ref_len") childArguments) current:=
    .scoped source _ _ _ _ values body callee shape returned childTarget args called (by omega) run checked
  obtain ⟨added,bounded,lengthCell,saved,_frame,_price⟩:=NodeRefLen.scoped_normal (ofString "rl2") childArguments installed reached
  have currentPayload : current.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (saved (ofString "payload") (by decide)).trans payloadCell
  obtain ⟨afterAdd,addRun,advanceRun⟩:=Input.sequence_none current inner addLength advance continued
  have read : eval current (.op .add [localVar "payload",localVar "rl2"])=some (.val (.word (payload+added))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,currentPayload,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have afterAddEq:=Input.assign_none current afterAdd "payload" (.op .add [localVar "payload",localVar "rl2"]) (payload+added) read addRun
  have keep:= (Input.LocalPrefix.assign (key:=ofString "payload") (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full afterAdd
  change Input.LocalSummary (ofString "payload") advance afterAdd at keep
  unfold Input.LocalSummary at keep
  rw [advanceRun] at keep
  have finalPayload : inner.locals.lookup (ofString "payload")=some (.val (.word (payload+added))):=by
    rw [keep.1 rfl,afterAddEq]
    exact bind_lookup_same _ _ _
  have frame:=scan_body_readonly source.code installed source rfl
  rw [normal] at frame
  refine ⟨added,bounded,scan_body_advance source target index indexCell normal,?_,frame⟩
  rw [endpoint,restore_lookup_other source inner "rl2" "payload" (by decide)]
  exact finalPayload

/-- The physical reference data determines the precise addition made by
this actual scan iteration, including the scoped result restoration. -/
theorem scan_iteration_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (index payload child tag cached length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) childArguments=some [.val (.word child)])
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached)
    (size : child≠0#64→tag≠0#64→cached≠0#64→source.memaddrs (child+16#64) ∧ source.memory (child+16#64)=.word length)
    (normal : evaluateHOLFiniteState source scanBody=(none,target)) :
    target.locals.lookup (ofString "i")=some (.val (.word (index+1#64))) ∧
      target.locals.lookup (ofString "payload")=some (.val (.word (payload+NodeRefLen.referenceWord child tag length))) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  let added:=NodeRefLen.referenceWord child tag length
  have shaped:=normal
  rw [scan_shapes.2.1] at shaped
  obtain ⟨funded,values,body,callee,shape,childTarget,returned,inner,args,called,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none_data source target "rl2" .one (ofString "node_ref_len") childArguments (.seq addLength advance) shaped
  let current:=Input.CallNormal.continuationEntry source childTarget "rl2" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "rl2") .one (ofString "node_ref_len") childArguments) current:=
    .scoped source _ _ _ _ values body callee shape returned childTarget args called (by omega) run checked
  obtain ⟨lengthCell,_populated,saved,_frame,_price⟩:=NodeRefLen.scoped_normal_exact (ofString "rl2") childArguments child tag cached length
    installed argsRead header cache size reached
  have currentPayload : current.locals.lookup (ofString "payload")=some (.val (.word payload)):=
    (saved (ofString "payload") (by decide)).trans payloadCell
  obtain ⟨afterAdd,addRun,advanceRun⟩:=Input.sequence_none current inner addLength advance continued
  have read : eval current (.op .add [localVar "payload",localVar "rl2"])=some (.val (.word (payload+added))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,currentPayload,lengthCell,added,valueIsWord,valueWord,wordOpHOL,wordOp]
  have afterAddEq:=Input.assign_none current afterAdd "payload" (.op .add [localVar "payload",localVar "rl2"]) (payload+added) read addRun
  have keep:= (Input.LocalPrefix.assign (key:=ofString "payload") (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full afterAdd
  change Input.LocalSummary (ofString "payload") advance afterAdd at keep
  unfold Input.LocalSummary at keep
  rw [advanceRun] at keep
  have finalPayload : inner.locals.lookup (ofString "payload")=some (.val (.word (payload+added))):=by
    rw [keep.1 rfl,afterAddEq]
    exact bind_lookup_same _ _ _
  have frame:=scan_body_readonly source.code installed source rfl
  rw [normal] at frame
  refine ⟨scan_body_advance source target index indexCell normal,?_,frame⟩
  rw [endpoint,restore_lookup_other source inner "rl2" "payload" (by decide)]
  exact finalPayload

/-- Sixteen real reference results contribute at most528 bytes in total.
The source payload and this bound prove that the actual additions do not
wrap. The scan leaves every nonlocal field unchanged. -/
theorem scan_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (fits : payload.toNat+528<2^64)
    (normal : evaluateHOLFiniteState source scanLoop=(none,target)) :
    (∃ result : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word result)) ∧ result.toNat≤payload.toNat+528) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ index value : BitVec 64,
    current.locals.lookup (ofString "i")=some (.val (.word index)) ∧ current.locals.lookup (ofString "payload")=some (.val (.word value)) ∧
      index.toNat≤16 ∧ value.toNat≤payload.toNat+33*index.toNat
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) scanBody=(none,post)→invariant post:=by
    intro current codeEq ⟨index,value,indexCell,payloadCell,bounded,amount⟩ word observed nonzero _funded post run
    have small : index.toNat<9223372036854775808:=by omega
    have expected : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=
        some (.val (.word (if index.toNat<16 then 1#64 else 0#64))):=by
      simp [scanTest,evalHOLFinite,evalHOLExact,toExact,localVar,indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]
    have active : index.toNat<16:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using observed.symm.trans expected
      exact nonzero zero
    have currentInstalled : Input.OriginalCode.Installed current.code:=by rw [codeEq]; exact installed
    obtain ⟨added,bound,indexAfter,payloadAfter,_frame⟩:=scan_iteration_normal (decClockHOLFinite current) post index value currentInstalled indexCell payloadCell run
    have indexNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]; rfl
    have amountNumber : (value+added).toNat=value.toNat+added.toNat:=BitVec.toNat_add_of_lt (by omega)
    exact ⟨index+1#64,value+added,indexAfter,payloadAfter,by rw [indexNumber]; omega,by rw [amountNumber,indexNumber]; omega⟩
  have shaped:=normal
  rw [scan_shapes.1] at shaped
  obtain ⟨index,result,_indexAfter,payloadAfter,bounded,amount⟩:=Input.loop_invariant source.code (ofString "node") scanTest scanBody scan_body_safe invariant step source target rfl
    ⟨0#64,payload,indexCell,payloadCell,by decide,by simp⟩ shaped
  have frame:=Input.LocalEffects.loop source.code scanTest scanBody (scan_body_readonly source.code installed) source rfl
  rw [shaped] at frame
  exact ⟨⟨result,payloadAfter,by omega⟩,frame⟩

/-- The real sixteen child slots and the header/cache words used by the
length scan. No normal return or future writer allocation is assumed. -/
structure ReferenceScanData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) where
  child : Nat→BitVec 64
  tag : Nat→BitVec 64
  cached : Nat→BitVec 64
  length : Nat→BitVec 64
  slot : ∀ i,i<16→source.memaddrs (node+32#64+BitVec.ofNat 64 i*8#64) ∧
    source.memory (node+32#64+BitVec.ofNat 64 i*8#64)=.word (child i)
  header : ∀ i,i<16→child i≠0#64→source.memaddrs (child i) ∧ source.memory (child i)=.word (tag i)
  cache : ∀ i,i<16→child i≠0#64→tag i≠0#64→source.memaddrs (child i+8#64) ∧ source.memory (child i+8#64)=.word (cached i)
  size : ∀ i,i<16→child i≠0#64→tag i≠0#64→cached i≠0#64→source.memaddrs (child i+16#64) ∧ source.memory (child i+16#64)=.word (length i)

def ReferenceScanData.of_frame {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (frame : Input.LocalEffects.erase current=Input.LocalEffects.erase source) : ReferenceScanData current node := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change current.memaddrs=source.memaddrs at domain
  have memory:=Input.LocalEffects.memory_of_erase source current frame
  exact {child:=data.child,tag:=data.tag,cached:=data.cached,length:=data.length
         slot:=by simpa only [domain,memory] using data.slot
         header:=by simpa only [domain,memory] using data.header
         cache:=by simpa only [domain,memory] using data.cache
         size:=by simpa only [domain,memory] using data.size}

def ReferenceScanData.word {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (i : Nat) : BitVec 64:=NodeRefLen.referenceWord (data.child i) (data.tag i) (data.length i)

def ReferenceScanData.total {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) : Nat→Nat
  | 0=>0
  | i+1=>data.total i+(data.word i).toNat

theorem ReferenceScanData.total_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (i : Nat) : data.total i≤33*i := by
  induction i with
  | zero=>simp only [total,Nat.mul_zero,Nat.le_refl]
  | succ i ih=>
    have bound:=NodeRefLen.reference_bound (data.child i) (data.tag i) (data.length i)
    change (data.word i).toNat≤33 at bound
    simp only [total]
    omega

theorem ReferenceScanData.arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (index : BitVec 64) (active : index.toNat<16)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) childArguments=some [.val (.word (data.child index.toNat))] := by
  obtain ⟨mapped,stored⟩:=data.slot index.toNat active
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] at mapped stored
  simp [childArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

/-- The actual completed scan adds exactly the sum of its sixteen real
reference lengths. This is the payload budget for the later writer loop. -/
theorem scan_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node payload : BitVec 64)
    (data : ReferenceScanData source node) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (fits : payload.toNat+528<2^64)
    (normal : evaluateHOLFiniteState source scanLoop=(none,target)) :
    (∃ result : BitVec 64,target.locals.lookup (ofString "payload")=some (.val (.word result)) ∧
      result.toNat=payload.toNat+data.total 16) ∧
      target.locals.lookup (ofString "i")=some (.val (.word 16#64)) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ index value : BitVec 64,
    current.locals.lookup (ofString "i")=some (.val (.word index)) ∧ current.locals.lookup (ofString "payload")=some (.val (.word value)) ∧
      index.toNat≤16 ∧ value.toNat=payload.toNat+data.total index.toNat ∧
      current.locals.lookup (ofString "node")=some (.val (.word node)) ∧ Input.LocalEffects.erase current=Input.LocalEffects.erase source
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) scanBody=(none,post)→invariant post:=by
    intro current codeEq ⟨index,value,currentIndex,currentPayload,bounded,amount,currentNode,frame⟩ word observed nonzero _funded post run
    have small : index.toNat<9223372036854775808:=by omega
    have expected : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) scanTest=
        some (.val (.word (if index.toNat<16 then 1#64 else 0#64))):=by
      simp [scanTest,evalHOLFinite,evalHOLExact,toExact,localVar,currentIndex,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]
    have active : index.toNat<16:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using observed.symm.trans expected
      exact nonzero zero
    let ready:=decClockHOLFinite current
    let currentData : ReferenceScanData ready node:=data.of_frame frame
    have currentInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed
    obtain ⟨indexAfter,payloadAfter,nextFrame⟩:=scan_iteration_normal_exact ready post index value (data.child index.toNat) (data.tag index.toNat) (data.cached index.toNat) (data.length index.toNat)
      currentInstalled currentIndex currentPayload (currentData.arguments index active currentNode currentIndex)
      (currentData.header index.toNat active) (currentData.cache index.toNat active) (currentData.size index.toNat active) run
    have indexNumber : (index+1#64).toNat=index.toNat+1:=by rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]; rfl
    have sumBound:=data.total_bound index.toNat
    have addedBound:=NodeRefLen.reference_bound (data.child index.toNat) (data.tag index.toNat) (data.length index.toNat)
    have amountNumber : (value+data.word index.toNat).toNat=value.toNat+(data.word index.toNat).toNat:=BitVec.toNat_add_of_lt (by change (data.word index.toNat).toNat≤33 at addedBound; omega)
    have saved:=scan_body_safe.summary_full ready
    unfold Input.LocalSummary at saved
    rw [run] at saved
    refine ⟨index+1#64,value+data.word index.toNat,indexAfter,payloadAfter,?_,?_,(saved.1 rfl).trans currentNode,nextFrame.trans frame⟩
    · rw [indexNumber]; omega
    · rw [amountNumber,indexNumber,ReferenceScanData.total,amount]; omega
  have shaped:=normal
  rw [scan_shapes.1] at shaped
  obtain ⟨index,result,finalIndex,finalPayload,bounded,amount,_finalNode,frame⟩:=Input.loop_invariant source.code (ofString "node") scanTest scanBody scan_body_safe invariant step source target rfl
    ⟨0#64,payload,indexCell,payloadCell,by decide,by simp [ReferenceScanData.total],nodeCell,rfl⟩ shaped
  have noBreak : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState current scanBody).1≠some .break:=by
    intro current
    have safe:=scan_body_safe.summary_full current
    exact safe.2.2.1
  have exit:=Input.loop_normal_exit scanTest scanBody noBreak source target shaped
  have small : index.toNat<9223372036854775808:=by omega
  have inactive : ¬index.toNat<16:=by
    have expected : evalHOLFinite target (h:=fun address=>Classical.propDecidable (target.memaddrs address)) scanTest=
        some (.val (.word (if index.toNat<16 then 1#64 else 0#64))):=by
      simp [scanTest,evalHOLFinite,evalHOLExact,toExact,localVar,finalIndex,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]
    intro active
    rw [if_pos active,exit] at expected
    cases expected
  have count : index.toNat=16:=by omega
  have indexEq : index=16#64:=by apply BitVec.eq_of_toNat_eq; exact count
  exact ⟨⟨result,finalPayload,by simpa only [count] using amount⟩,by simpa only [indexEq] using finalIndex,frame⟩

/-- Exactly the stable child words needed by the finish length and write
loops. The separately mutable HASH24 word is outside this read set. -/
def ReferenceScanData.Footprint {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (query : BitVec 64) : Prop:=
  ∃ i,i<16 ∧ (query=node+32#64+BitVec.ofNat 64 i*8#64 ∨
    (data.child i≠0#64 ∧ (query=data.child i ∨ (data.tag i≠0#64 ∧
      (query=data.child i+8#64 ∨ (data.cached i≠0#64 ∧ query=data.child i+16#64))))))

/-- Transport the actual reference inputs through a normal writer whose
real effects preserve these source queries; every other word may change. -/
def ReferenceScanData.of_memory {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (domain : current.memaddrs=source.memaddrs)
    (agree : ∀ query,data.Footprint query→current.memory query=source.memory query) : ReferenceScanData current node := {
  child:=data.child,tag:=data.tag,cached:=data.cached,length:=data.length
  slot:=by
    intro i inside
    obtain ⟨mapped,stored⟩:=data.slot i inside
    exact ⟨by rw [domain]; exact mapped,(agree _ ⟨i,inside,Or.inl rfl⟩).trans stored⟩
  header:=by
    intro i inside active
    obtain ⟨mapped,stored⟩:=data.header i inside active
    exact ⟨by rw [domain]; exact mapped,(agree _ ⟨i,inside,Or.inr ⟨active,Or.inl rfl⟩⟩).trans stored⟩
  cache:=by
    intro i inside active nonHash
    obtain ⟨mapped,stored⟩:=data.cache i inside active nonHash
    exact ⟨by rw [domain]; exact mapped,(agree _ ⟨i,inside,Or.inr ⟨active,Or.inr ⟨nonHash,Or.inl rfl⟩⟩⟩).trans stored⟩
  size:=by
    intro i inside active nonHash populated
    obtain ⟨mapped,stored⟩:=data.size i inside active nonHash populated
    exact ⟨by rw [domain]; exact mapped,(agree _ ⟨i,inside,Or.inr ⟨active,Or.inr ⟨nonHash,Or.inr ⟨populated,rfl⟩⟩⟩⟩).trans stored⟩ }

theorem ReferenceScanData.total_mono {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (first last : Nat) (ordered : first≤last) : data.total first≤data.total last := by
  induction last with
  | zero=>
    have equal : first=0:=by omega
    rw [equal]
  | succ last ih=>
    by_cases equal : first=last+1
    · rw [equal]
    · have earlier:=ih (by omega)
      simp only [ReferenceScanData.total]
      omega


/-- Every existing physical cell has the word represented by wordAt. -/
theorem reference_word_stored (memory : GasBudget.Memory) (pointer : BitVec 64) :
    memory pointer=.word (GasBudget.wordAt memory pointer) := by
  cases stored : memory pointer with
  | word word=>simp [GasBudget.wordAt,stored,MemoryBytes.wordBits]

/-- An actual registered node allocation maps its three cache words,
independently of whether any cache has yet been populated. -/
theorem reference_cache_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (lower upper : Nat) (regions : graph.Regions lower upper)
    (domain : source.memaddrs=InitE.ordinaryDomain) (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (offset : Nat) (inside : offset<32) (aligned : offset%8=0) : source.memaddrs (byteAddress node offset) := by
  obtain ⟨_floor,arena,nodeAligned,_before⟩:=regions node member active
  have minimum:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory node)
  exact AllocatedBytes.word_mapped source node (TrieWalk.nodeBytes (GasBudget.wordAt source.memory node)) offset domain arena
    (by omega) nodeAligned aligned

/-- Any truthful reference-scan view obtains child membership from the
actual parent's registered sixteen-slot branch view. -/
theorem ReferenceScanData.child_member {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : GasBudget.wordAt source.memory node=3#64)
    (i : Nat) (inside : i<16) : graph.valid (data.child i) := by
  let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) i inside
  have slot:=data.slot i inside
  have address : BitVec.ofNat 64 (i*8)=BitVec.ofNat 64 i*8#64:=by rw [BitVec.ofNat_mul]
  have stored : source.memory (node+32#64+BitVec.ofNat 64 i*8#64)=.word view.child:=by
    simpa only [address] using view.stored
  have same : data.child i=view.child:=HolWordLab.word.inj (slot.2.symm.trans stored)
  rw [same]
  exact view.member

/-- Construct the actual reference inputs from the registered parent and
node allocation regions. Unused lengths are zero; no future read or normal
callee return is an input. -/
noncomputable def ReferenceScanData.of_graph (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt source.memory node=3#64) (lower upper : Nat) (regions : graph.Regions lower upper)
    (domain : source.memaddrs=InitE.ordinaryDomain) : ReferenceScanData source node := by
  let child:=fun i : Nat=>GasBudget.wordAt source.memory (node+32#64+BitVec.ofNat 64 i*8#64)
  let childTag:=fun i=>GasBudget.wordAt source.memory (child i)
  let cached:=fun i=>GasBudget.wordAt source.memory (child i+8#64)
  let length:=fun i=>if child i=0#64 ∨ childTag i=0#64 ∨ cached i=0#64 then 0#64 else GasBudget.wordAt source.memory (child i+16#64)
  have children : ∀ i,i<16 → graph.valid (child i):=by
    intro i inside
    let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) i inside
    have address : BitVec.ofNat 64 (i*8)=BitVec.ofNat 64 i*8#64:=by rw [BitVec.ofNat_mul]
    have stored : source.memory (node+32#64+BitVec.ofNat 64 i*8#64)=.word view.child:=by
      simpa only [address] using view.stored
    have same : child i=view.child:=by simp only [child,GasBudget.wordAt,stored,MemoryBytes.wordBits]
    rw [same]
    exact view.member
  refine ⟨child,childTag,cached,length,?_,?_,?_,?_⟩
  · intro i inside
    have view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) i inside
    have address : BitVec.ofNat 64 (i*8)=BitVec.ofNat 64 i*8#64:=by rw [BitVec.ofNat_mul]
    exact ⟨by rw [←address]; exact view.mapped,reference_word_stored source.memory _⟩
  · intro i inside live
    exact graph.header _ (children i inside) live
  · intro i inside live _nonHash
    exact ⟨reference_cache_mapped source graph lower upper regions domain _ (children i inside) live 8 (by decide) (by decide),reference_word_stored source.memory _⟩
  · intro i inside live nonHash populated
    have relevant : ¬(child i=0#64 ∨ childTag i=0#64 ∨ cached i=0#64):=by
      rintro (zero|zero|zero)
      · exact live zero
      · exact nonHash zero
      · exact populated zero
    refine ⟨reference_cache_mapped source graph lower upper regions domain _ (children i inside) live 16 (by decide) (by decide),?_⟩
    simp only [length,if_neg relevant]
    exact reference_word_stored source.memory _

/-- Reference inputs occupy actual registered node fields, excluding the
mutable HASH24 word. Repeated child pointers need no tree assumption. -/
theorem ReferenceScanData.Footprint.location {source : PanSemStateFiniteExact 64 Guest.HostMemory} {node : BitVec 64}
    (data : ReferenceScanData source node) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (member : graph.valid node) (active : node≠0#64) (tag : GasBudget.wordAt source.memory node=3#64)
    (query : BitVec 64) (required : data.Footprint query) :
    ∃ owner offset,graph.valid owner ∧ owner≠0#64 ∧ offset<TrieWalk.nodeBytes (GasBudget.wordAt source.memory owner) ∧ offset≠24 ∧ query=byteAddress owner offset := by
  obtain ⟨i,inside,slot|⟨live,header|⟨nonHash,cache|⟨populated,size⟩⟩⟩⟩:=required
  · refine ⟨node,32+i*8,member,active,?_,by omega,?_⟩
    · rw [tag]; change 32+i*8<176; omega
    · rw [slot,byteAddress,BitVec.ofNat_add,BitVec.ofNat_mul]
      exact BitVec.add_assoc _ _ _
  · refine ⟨data.child i,0,data.child_member graph member active tag i inside,live,?_,by decide,?_⟩
    · have bound:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i)); omega
    · simpa [byteAddress] using header
  · refine ⟨data.child i,8,data.child_member graph member active tag i inside,live,?_,by decide,cache⟩
    have bound:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i)); omega
  · refine ⟨data.child i,16,data.child_member graph member active tag i inside,live,?_,by decide,size⟩
    have bound:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt source.memory (data.child i)); omega


/-- A bound on existing populated non-hash RLP caches. Its actual producer
must be retained through constructors and completed serialization. -/
def CachedLengths {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit : Nat) : Prop :=
  ∀ node,graph.valid node → node≠0#64 → GasBudget.wordAt source.memory node≠0#64 →
    GasBudget.wordAt source.memory (node+8#64)≠0#64 → (GasBudget.wordAt source.memory (node+16#64)).toNat≤limit

/-- Only an actual populated non-hash cache consumes the cached-length
bound; null/hash/missing-cache cases choose zero for their unused length. -/
theorem ReferenceScanData.of_graph_lengths (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid node) (active : node≠0#64)
    (tag : GasBudget.wordAt source.memory node=3#64) (lower upper : Nat) (regions : graph.Regions lower upper)
    (domain : source.memaddrs=InitE.ordinaryDomain) (limit : Nat) (bounded : CachedLengths graph limit)
    (i : Nat) (inside : i<16) :
    ((ReferenceScanData.of_graph source node graph member active tag lower upper regions domain).length i).toNat≤limit := by
  let child:=GasBudget.wordAt source.memory (node+32#64+BitVec.ofNat 64 i*8#64)
  change (if child=0#64 ∨ GasBudget.wordAt source.memory child=0#64 ∨ GasBudget.wordAt source.memory (child+8#64)=0#64
    then 0#64 else GasBudget.wordAt source.memory (child+16#64)).toNat≤limit
  split
  · change 0≤limit; omega
  · rename_i relevant
    have live : child≠0#64:=fun zero=>relevant (Or.inl zero)
    have nonHash : GasBudget.wordAt source.memory child≠0#64:=fun zero=>relevant (Or.inr (Or.inl zero))
    have populated : GasBudget.wordAt source.memory (child+8#64)≠0#64:=fun zero=>relevant (Or.inr (Or.inr zero))
    exact bounded child ((ReferenceScanData.of_graph source node graph member active tag lower upper regions domain).child_member graph member active tag i inside) live nonHash populated

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_body_readonly
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_iteration_normal
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_iteration_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.total_bound
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_normal_exact

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.total_mono

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.reference_word_stored
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.reference_cache_mapped
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.child_member
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.of_graph
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.Footprint.location

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.ReferenceScanData.of_graph_lengths
