import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.Input.ContinuingDeclarationEntry
import InitECandidate.Solver.Input.RlpWrite.U256Shape
import InitECandidate.Solver.Input.CurrentRlp.WordWrite
import InitECandidate.Solver.Input.RlpWrite.Access
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

abbrev body:=Code.body .writeBytes

theorem current_body : body=RlpWrite.BytesWrite.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_encode_bytes")=some (RlpWrite.BytesWrite.formals,body,.one) := by
  have known:=Code.installed code installed .writeBytes
  simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_encode_bytes,RlpWrite.BytesWrite.formals,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

theorem helper_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : RlpWrite.BytesWrite.Codes source := by
  refine ⟨?_,?_,?_,CopyGeneral.original_code source.code installed⟩
  · simpa only [HeaderWrite.current_body] using HeaderWrite.original_code source.code installed
  · simpa only [RlpLength.Be.formals,BeLength.current_body] using BeLength.original_code source.code installed
  · simpa only [PutBe.current_body] using PutBe.original_code source.code installed

/-- The actual current byte-string writer derives all reads/stores from
its owned input/output extents. These are the physical ranges retained by
the real header prefix, not hypotheses about any future helper return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat)
    (small : length≤134217712) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst (length+9)) (funded : length+20≤source.clock) :
    ∃ target encoded paid,length≤encoded ∧ 1≤encoded ∧ encoded≤length+9 ∧ paid≤length+20 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      target.clock=source.clock-paid ∧ WriteFrame source target dst (length+9) := by
  obtain ⟨byte,access⟩:=RlpWrite.bytes_access source dst src length small domain srcArena dstArena
  have codes:=helper_codes source installed
  obtain ⟨target,encoded,paid,lower,positive,upper,bound,number,run,frame,memory⟩:=RlpWrite.BytesWrite.execute source dst src length byte small d s n access.loaded
    codes.header codes.beCode codes.put codes.copyCode access.headerMapped access.copyMapped funded
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change target.clock=source.clock-paid at clock
  have metadata:=congrArg MemoryMetadata.erase frame
  exact ⟨target,encoded,paid,lower,positive,upper,bound,number,run,clock,metadata,memory⟩

/-- Short entry clocks and all other outcomes obey the same bound. The
actual range assumptions come from the caller's earlier physical proof. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat)
    (small : length≤134217712) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst (length+9)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length+20 := by
  by_cases funded : length+20≤source.clock
  · obtain ⟨target,encoded,paid,lower,positive,upper,bound,number,run,clock,frame⟩:=execute source dst src length small installed domain d s n srcArena dstArena funded
    rw [run]
    change source.clock-target.clock≤length+20
    omega
  · omega

/-- Actual normal returns, including clocks below the allowance, retain
the genuine encoded length, nonlocal state and bounded destination frame. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat)
    (small : length≤134217712) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst (length+9))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,length≤encoded ∧ 1≤encoded ∧ encoded≤length+9 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ source.clock-target.clock≤length+20 ∧ WriteFrame source target dst (length+9) := by
  let padding:=length+20
  let padded:={source with clock:=source.clock+padding}
  obtain ⟨post,encoded,paid,lower,positive,upper,bound,number,run,clock,frame⟩:=execute padded dst src length small installed domain d s n srcArena dstArena (by change padding≤source.clock+padding; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target padding ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+padding}=post at endpoint
  rw [←endpoint] at frame
  have cost:=body_cost source dst src length small installed domain d s n srcArena dstArena
  rw [normal] at cost
  exact ⟨encoded,lower,positive,upper,number,answer,cost,frame.metadata,frame.memory⟩

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst src : BitVec 64) (length : Nat)
    (small : length≤134217712) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst (length+9))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_bytes") arguments)).2.clock≤length+21 := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src (BitVec.ofNat 64 length) (original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "rlp_encode_bytes") arguments _ body callee .one (length+20) args called
    (body_cost (callEntryStateHOLFinite source callee) dst src length small installed domain d s n srcArena dstArena)

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst src : BitVec 64) (length : Nat)
    (small : length≤134217712) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst (length+9))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_encode_bytes") arguments)=(none,post)) : WriteFrame source post dst (length+9) := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src (BitVec.ofNat 64 length) (original_code source.code installed)
  apply WriteFrame.ignored source post (ofString "rlp_encode_bytes") arguments _ body callee .one dst (length+9) args called
  · intro target value run
    obtain ⟨encoded,lower,positive,upper,number,answer,cost,frame⟩:=body_normal (callEntryStateHOLFinite source callee) target dst src length small installed domain d s n srcArena dstArena value run
    exact frame
  · exact normal

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.helper_codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.execute
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.call_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.call_frame

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite.BytesWrite

/-- The actual single-byte decision spends no source ticks on any outcome. -/
theorem first_guard_cost (code) : ClockCost.Bound code firstGuard 0 := by
  apply ClockCost.conditional code _ _ _ 0 0
  · apply ClockCost.declared code (ofString "b") .one (.loadByte (localVar "src")) byteBranch 0
    exact ClockCost.conditional code _ _ _ 0 0 (HeaderWrite.short_cost code _) (ClockCost.skip code)
  · exact ClockCost.skip code

/-- A genuine fallthrough took only skipped branches and restored b.
A writing short-form branch must stop, including on a failed store. -/
theorem first_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (normal : evaluateHOLFiniteState source firstGuard=(none,post)) : post=source := by
  rcases conditional_none source post oneTest oneBranch .skip normal with one|skipped
  · obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=CallNormal.declaration_continuing_entry source post "b" .one
      (.loadByte (localVar "src")) byteBranch one
    obtain ⟨word,rfl⟩:=RlpWrite.U256Value.scalar_word declared ((shapeEqHOL_eq_true _ _).mp checked).symm
    let entry:=bind source "b" word
    rcases conditional_none entry inner byteTest (RlpWrite.shortForm (localVar "b")) .skip continued with short|skipped
    · exact (HeaderWrite.short_stops entry (localVar "b") (congrArg Prod.fst short)).elim
    · have same : inner=entry:=by simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm
      rw [endpoint,same]
      exact restore_bound source "b" word
  · simpa only [evaluateHOLFiniteState_skip] using (congrArg Prod.snd skipped).symm

/-- The real header child supplies its scalar result and actual caller
clock. The copy allowance is instantiated below by checked current bodies. -/
theorem general_current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word count))) (copyPrice : Nat)
    (copyBody : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ output : BitVec 64,
      current.memaddrs=InitE.ordinaryDomain→current.locals.lookup (ofString "dst")=some (.val (.word output))→
      current.locals.lookup (ofString "n")=some (.val (.word count))→
      current.clock-(evaluateHOLFiniteState current Copy32.body).2.clock≤copyPrice) :
    source.clock-(evaluateHOLFiniteState source generalTail).2.clock≤copyPrice+20 := by
  have headerCode : source.code.lookup (ofString "rlp_write_header")=some (RlpWrite.HeaderWrite.formals,RlpWrite.HeaderWrite.body,.one):=
    HeaderWrite.original_code source.code installed
  obtain ⟨callee,called,childD,childBase,childN⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst 128#64 count headerCode
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [localVar "dst",.const 128#64,localVar "n"]=some [.val (.word dst),.val (.word 128#64),.val (.word count)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  have bounded:=ClockCost.scoped_reached_current source "h" .one (ofString "rlp_write_header")
    [localVar "dst",.const 128#64,localVar "n"] _ RlpWrite.HeaderWrite.body generalAfterHeader callee .one 18 (copyPrice+1)
    args called (HeaderWrite.body_cost (callEntryStateHOLFinite source callee) dst count installed childD childN) (by
      intro target returned run checked
      obtain ⟨encoded,positive,small,answer,price,frame⟩:=HeaderWrite.body_normal (callEntryStateHOLFinite source callee) target dst count installed childD childN returned run
      let ready:=CallNormal.continuationEntry source target "h" returned
      have codeEq : ready.code=source.code:=MemoryMetadata.code frame.metadata
      have currentDomain : ready.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain frame.metadata).trans domain
      have currentInstalled : OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
      have currentD : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
        (CallNormal.continuation_lookup_other source target "h" "dst" returned (by decide)).trans d
      have currentS : ready.locals.lookup (ofString "src")=some (.val (.word src)):=
        (CallNormal.continuation_lookup_other source target "h" "src" returned (by decide)).trans s
      have currentN : ready.locals.lookup (ofString "n")=some (.val (.word count)):=
        (CallNormal.continuation_lookup_other source target "h" "n" returned (by decide)).trans n
      have currentH : ready.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 encoded))):=by
        exact (CallNormal.continuation_lookup_same source target "h" returned).trans (congrArg some answer)
      let output:=dst+BitVec.ofNat 64 encoded
      have copyArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query))
          [.op .add [localVar "dst",localVar "h"],localVar "src",localVar "n"]=some (CopyGeneral.values output src count.toNat):=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentD,currentS,currentN,currentH,
          valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values,output]
      obtain ⟨copyCallee,copyCalled,copyD,copyS,copyN⟩:=CopyGeneral.environment ready.code.lookup output src count.toNat
        (CopyGeneral.original_code ready.code currentInstalled)
      have countCell : copyCallee.lookup (ofString "n")=some (.val (.word count)):=by
        simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using copyN
      have copied:=ClockCost.call_current ready (some none) (ofString "memcpy") _ (CopyGeneral.values output src count.toNat)
        Copy32.body copyCallee .one copyPrice copyArgs copyCalled (copyBody (callEntryStateHOLFinite ready copyCallee) output currentDomain copyD countCell)
      have last:=ClockCost.sequence_current ready _ (.return (.op .add [localVar "h",localVar "n"])) (copyPrice+1) 0 copied (ClockCost.returned ready.code _)
      simpa only [Nat.add_zero,generalAfterHeader,LocalEffects.callInfo,Option.map_some,Option.map_none,ready,CallNormal.continuationEntry,setVarHOLFinite] using last)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "h") .one (ofString "rlp_write_header")
    [localVar "dst",.const 128#64,localVar "n"] generalAfterHeader)).2.clock≤copyPrice+20
  omega

theorem body_current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word count))) (copyPrice : Nat)
    (copyBody : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ output : BitVec 64,
      current.memaddrs=InitE.ordinaryDomain→current.locals.lookup (ofString "dst")=some (.val (.word output))→
      current.locals.lookup (ofString "n")=some (.val (.word count))→
      current.clock-(evaluateHOLFiniteState current Copy32.body).2.clock≤copyPrice) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤copyPrice+20 := by
  rw [current_body,RlpWrite.BytesWrite.body_shape]
  have result:=ClockCost.sequence_reached_current source firstGuard generalTail 0 (copyPrice+20)
    (first_guard_cost source.code source rfl) (by
      intro middle normal
      have same:=first_guard_normal source middle normal
      rw [same]
      exact general_current_cost source dst src count installed domain d s n copyPrice copyBody)
  simpa only [Nat.zero_add] using result

/-- No ownership or future byte/header/copy success is supplied. -/
theorem body_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word count))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤43314052495 := by
  apply body_current_cost source dst src count installed domain d s n 43314052475
  intro current output currentDomain currentD currentN
  exact Nat.le_trans (CopyAny.body_domain_cost current output currentDomain currentD) (CopyAny.domain_price_uniform output)

/-- Known actual lengths retain the smaller length-based copy allowance,
without source/destination ownership or later success premises. -/
theorem body_known_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat)
    (small : length+32<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤CopyAny.price length+20 := by
  apply body_current_cost source dst src (BitVec.ofNat 64 length) installed domain d s n (CopyAny.price length)
  intro current output currentDomain currentD currentN
  exact CopyAny.body_cost current length small currentN

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.first_guard_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.first_guard_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.general_current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_domain_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_known_length_cost

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original ignored, assigned and tail-call forms share the same actual
three-word ABI and add their own single caller tick. -/
theorem call_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (dst src count : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word count)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_encode_bytes") arguments)).2.clock≤43314052496 := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src count (original_code source.code installed)
  exact ClockCost.call_current source destination (ofString "rlp_encode_bytes") arguments _ body callee .one 43314052495 args called
    (body_domain_cost (callEntryStateHOLFinite source callee) dst src count installed domain d s n)

theorem call_known_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64)) (dst src : BitVec 64) (length : Nat)
    (small : length+32<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word (BitVec.ofNat 64 length))]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_encode_bytes") arguments)).2.clock≤CopyAny.price length+21 := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src (BitVec.ofNat 64 length) (original_code source.code installed)
  exact ClockCost.call_current source destination (ofString "rlp_encode_bytes") arguments _ body callee .one (CopyAny.price length+20) args called
    (body_known_length_cost (callEntryStateHOLFinite source callee) dst src length small installed domain d s n)

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.call_domain_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.call_known_length_cost
