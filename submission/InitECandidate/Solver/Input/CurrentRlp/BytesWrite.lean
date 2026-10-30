import InitECandidate.Solver.Input.ScalarArgumentsLookup
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

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite.BytesWrite

private theorem conditional_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (yes no : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.ite test yes no)=(some (.returned value),post)) :
    evaluateHOLFiniteState source yes=(some (.returned value),post) ∨
      evaluateHOLFiniteState source no=(some (.returned value),post) := by
  rw [evaluateHOLFiniteState_ite] at normal
  generalize read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun query=>Classical.propDecidable (source.memaddrs query)) test=observed at normal
  cases observed with
  | none=>cases normal
  | some observed=>
    cases observed with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero] at normal; exact Or.inr normal
        · rw [if_neg zero] at normal; exact Or.inl normal

/-- A genuine returning special case wrote one byte and returned its real
scalar one. The source-byte read and branch success come from this run. -/
theorem first_guard_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source firstGuard=(some (.returned value),post)) :
    value=.val (.word 1#64) ∧ WriteFrame source post dst 9 := by
  rcases conditional_return source post oneTest oneBranch .skip value normal with one|skipped
  · obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=CallNormal.declaration_normal_entry source post "b" .one
      (.loadByte (localVar "src")) byteBranch value one
    obtain ⟨word,rfl⟩:=RlpWrite.U256Value.scalar_word declared ((shapeEqHOL_eq_true _ _).mp checked).symm
    let entry:=bind source "b" word
    have entryD : entry.locals.lookup (ofString "dst")=some (.val (.word dst)):=
      (bind_lookup_other source "b" "dst" word (by decide)).trans d
    rcases conditional_return entry inner byteTest (RlpWrite.shortForm (localVar "b")) .skip value continued with short|skipped
    · obtain ⟨answer,frame⟩:=HeaderWrite.short_normal entry inner dst (localVar "b") entryD value short
      rw [endpoint]
      exact ⟨answer,frame.metadata,frame.memory⟩
    · simp [evaluateHOLFiniteState_skip] at skipped
  · simp [evaluateHOLFiniteState_skip] at skipped

/-- The header's actual scalar length and the real normal copy derive the
encoded byte count and full earlier-memory frame, without input ownership. -/
theorem general_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src count query : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (headerFits : dst.toNat+9<2^64) (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source generalTail=(some (.returned value),post)) :
    ∃ encoded,1≤encoded ∧ encoded≤count.toNat+9 ∧ encoded≤CopyAny.ordinaryEnd+40 ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      post.memory query=source.memory query := by
  have headerCode : source.code.lookup (ofString "rlp_write_header")=some (RlpWrite.HeaderWrite.formals,RlpWrite.HeaderWrite.body,.one):=
    HeaderWrite.original_code source.code installed
  obtain ⟨callee,called,childD,childBase,childN⟩:=RlpWrite.HeaderWrite.environment source.code.lookup dst 128#64 count headerCode
  have args : evalListHOLFinite source (h:=fun current=>Classical.propDecidable (source.memaddrs current))
      [localVar "dst",.const 128#64,localVar "n"]=some [.val (.word dst),.val (.word 128#64),.val (.word count)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,d,n]
  obtain ⟨funded,child,headerValue,inner,headerRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "h" .one
    (ofString "rlp_write_header") [localVar "dst",.const 128#64,localVar "n"] _ RlpWrite.HeaderWrite.body generalAfterHeader callee .one args called value normal
  obtain ⟨header,positive,small,answer,price,frame⟩:=HeaderWrite.body_normal (callEntryStateHOLFinite source callee) child dst count installed childD childN headerValue headerRun
  let ready:=CallNormal.continuationEntry source child "h" headerValue
  change evaluateHOLFiniteState ready generalAfterHeader=(some (.returned value),inner) at continued
  have codeEq : ready.code=source.code:=MemoryMetadata.code frame.metadata
  have currentDomain : ready.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain frame.metadata).trans domain
  have currentInstalled : OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  have currentD : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source child "h" "dst" headerValue (by decide)).trans d
  have currentS : ready.locals.lookup (ofString "src")=some (.val (.word src)):=
    (CallNormal.continuation_lookup_other source child "h" "src" headerValue (by decide)).trans s
  have currentN : ready.locals.lookup (ofString "n")=some (.val (.word count)):=
    (CallNormal.continuation_lookup_other source child "h" "n" headerValue (by decide)).trans n
  have currentH : ready.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 header))):=
    (CallNormal.continuation_lookup_same source child "h" headerValue).trans (congrArg some answer)
  let output:=dst+BitVec.ofNat 64 header
  have headerNumber : (BitVec.ofNat 64 header).toNat=header:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have outputNumber : output.toNat=dst.toNat+header:=by
    rw [BitVec.toNat_add_of_lt (by rw [headerNumber]; omega),headerNumber]
  have copyArgs : evalListHOLFinite ready (h:=fun current=>Classical.propDecidable (ready.memaddrs current))
      [.op .add [localVar "dst",localVar "h"],localVar "src",localVar "n"]=some (CopyGeneral.values output src count.toNat):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,currentD,currentS,currentN,currentH,
      valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values,output]
  have ignored : LocalPrefix (ofString "_") (.call (some (none,none)) (ofString "memcpy")
      [.op .add [localVar "dst",localVar "h"],localVar "src",localVar "n"]):=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨copied,copyRun,returned⟩:=sequence_returned ready inner _ _ value (ignored.summary_full ready).2.1 continued
  obtain ⟨countBound,copyFrame,copyMemory⟩:=CopyAny.call_domain_normal ready copied _ output src query count.toNat floor currentDomain copyArgs
    (CopyGeneral.original_code ready.code currentInstalled) aligned (by rw [outputNumber]; omega) beforeFloor copyRun
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq] at countBound
  have afterH : copied.locals.lookup (ofString "h")=some (.val (.word (BitVec.ofNat 64 header))):=
    (CallNormal.ignored_lookup ready copied (ofString "h") (ofString "memcpy") _ copyRun).trans currentH
  have afterN : copied.locals.lookup (ofString "n")=some (.val (.word count)):=
    (CallNormal.ignored_lookup ready copied (ofString "n") (ofString "memcpy") _ copyRun).trans currentN
  let encoded:=header+count.toNat
  have returnedRead : eval copied (.op .add [localVar "h",localVar "n"])=some (.val (.word (BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,afterH,afterN,valueIsWord,valueWord,wordOpHOL,wordOp,encoded,BitVec.ofNat_add]
  obtain ⟨actualRead,innerEq⟩:=return_normal copied inner (.op .add [localVar "h",localVar "n"]) value returned
  have valueEq : value=.val (.word (BitVec.ofNat 64 encoded)):=Option.some.inj (actualRead.symm.trans returnedRead)
  have roomBound : CopyAny.room output≤CopyAny.ordinaryEnd:=Nat.sub_le _ _
  have away : CopyGeneral.Away dst query 9:=CopyGeneral.Away.after_floor dst query 9 floor aligned afterFloor headerFits beforeFloor
  rw [endpoint,innerEq]
  exact ⟨encoded,by dsimp [encoded]; omega,by dsimp [encoded]; omega,by dsimp [encoded]; omega,valueEq,
    copyFrame.trans frame.metadata,copyMemory.trans (frame.memory query away)⟩

theorem body_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src count query : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (s : source.locals.lookup (ofString "src")=some (.val (.word src)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (headerFits : dst.toNat+9<2^64) (aligned : floor%8=0) (afterFloor : floor≤dst.toNat) (beforeFloor : query.toNat<floor)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ encoded,1≤encoded ∧ encoded≤count.toNat+9 ∧ encoded≤CopyAny.ordinaryEnd+40 ∧
      value=.val (.word (BitVec.ofNat 64 encoded)) ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      post.memory query=source.memory query := by
  rw [current_body,RlpWrite.BytesWrite.body_shape,evaluateHOLFiniteState_seq_line780] at normal
  generalize front : evaluateHOLFiniteState source firstGuard=output at normal
  obtain ⟨result,current⟩:=output
  cases result with
  | none=>
    have same:=first_guard_normal source current front
    subst current
    exact general_current_normal source post dst src count query floor installed domain d s n headerFits aligned afterFloor beforeFloor value normal
  | some result=>
    cases result with
    | returned actual=>
      cases normal
      obtain ⟨answer,frame⟩:=first_guard_returned source post dst d value front
      have away : CopyGeneral.Away dst query 9:=CopyGeneral.Away.after_floor dst query 9 floor aligned afterFloor headerFits beforeFloor
      exact ⟨1,by decide,by omega,by unfold CopyAny.ordinaryEnd; omega,answer,frame.metadata,frame.memory query away⟩
    | error=>cases normal
    | timeOut=>cases normal
    | «break»=>cases normal
    | «continue»=>cases normal
    | exception identifier payload=>cases normal
    | finalFfi event=>cases normal

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.first_guard_returned
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.general_current_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.body_current_normal

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine assigned field-writer call derives one encoded length for its
real returned word and protects every earlier word below the output frontier. -/
theorem assigned_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (arguments : List (ExpHOL 64)) (dst src count : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word dst),.val (.word src),.val (.word count)])
    (headerFits : dst.toNat+9<2^64) (positiveFloor : 0<floor) (aligned : floor%8=0) (afterFloor : floor≤dst.toNat)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "rlp_encode_bytes") arguments)=(none,post)) :
    ∃ encoded,1≤encoded ∧ encoded≤count.toNat+9 ∧ encoded≤CopyAny.ordinaryEnd+40 ∧
      post.locals.lookup name=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<floor→post.memory query=source.memory query) ∧
      ∀ key : MlS,key≠name→post.locals.lookup key=source.locals.lookup key := by
  obtain ⟨callee,called,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src count (original_code source.code installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,child,returned,actualArgs,actualCalled,run,checked,endpoint⟩:=
    CallNormal.local_data source post name (ofString "rlp_encode_bytes") arguments normal
  have sameValues : actualValues=[.val (.word dst),.val (.word src),.val (.word count)]:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have same : (actualBody,actualCallee,actualShape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases same
  obtain ⟨encoded,positive,upper,uniform,answer,metadata,memory⟩:=body_current_normal (callEntryStateHOLFinite source callee) child
    dst src count 0#64 floor installed domain d s n headerFits aligned afterFloor positiveFloor returned run
  refine ⟨encoded,positive,upper,uniform,?_,?_,?_,?_⟩
  · rw [endpoint,answer]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · rw [endpoint]
    exact metadata
  · intro query before
    obtain ⟨_,_,_,_,_,_,otherMemory⟩:=body_current_normal (callEntryStateHOLFinite source callee) child
      dst src count query floor installed domain d s n headerFits aligned afterFloor before returned run
    rw [endpoint]
    exact otherMemory
  · intro key different
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.assigned_current_normal

namespace InitECandidate.Solver.Input.CurrentRlp.BytesWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem argument_values (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second third : ExpHOL 64) (values : List (ValueHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,third]=some values) :
    ∃ left middle right,eval source first=some left ∧ eval source second=some middle ∧ eval source third=some right ∧ values=[left,middle,right] := by
  cases firstRead : eval source first with
  | none=>
    simp only [eval] at firstRead
    simp [evalListHOLFinite,evalListHOLExact,firstRead] at args
  | some left=>
    simp only [eval] at firstRead
    cases secondRead : eval source second with
    | none=>
      simp only [eval] at secondRead
      simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead] at args
    | some middle=>
      simp only [eval] at secondRead
      cases thirdRead : eval source third with
      | none=>
        simp only [eval] at thirdRead
        simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead,thirdRead] at args
      | some right=>
        simp only [eval] at thirdRead
        have same : [left,middle,right]=values:=by
          simpa only [evalListHOLFinite,evalListHOLExact,firstRead,secondRead,thirdRead,Option.some.injEq] using args
        exact ⟨left,middle,right,rfl,rfl,rfl,same.symm⟩

/-- A successful actual ABI lookup derives all three word reads and their
real callee bindings. Failed expression reads and shapes supply no entry. -/
theorem current_argument_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second third : ExpHOL 64) (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,third]=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "rlp_encode_bytes") values=some (actual,callee,shape)) :
    ∃ dst src count : BitVec 64,values=[.val (.word dst),.val (.word src),.val (.word count)] ∧
      eval source first=some (.val (.word dst)) ∧ eval source second=some (.val (.word src)) ∧ eval source third=some (.val (.word count)) ∧
      actual=body ∧ callee.lookup (ofString "dst")=some (.val (.word dst)) ∧
      callee.lookup (ofString "src")=some (.val (.word src)) ∧ callee.lookup (ofString "n")=some (.val (.word count)) := by
  obtain ⟨left,middle,right,firstRead,secondRead,thirdRead,valuesEq⟩:=argument_values source first second third values args
  rw [valuesEq] at called
  obtain ⟨dst,src,count,firstEq,secondEq,thirdEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n") body actual .one shape (original_code source.code installed) left middle right callee called
  subst left
  subst middle
  subst right
  obtain ⟨expected,expectedCall,d,s,n⟩:=RlpWrite.BytesWrite.environment source.code.lookup dst src count (original_code source.code installed)
  have same:=Option.some.inj (called.symm.trans expectedCall)
  have bodyEq : actual=body:=congrArg Prod.fst same
  have calleeEq : callee=expected:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [←calleeEq] at d s n
  exact ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩

/-- Every outcome of an actual dynamic byte-field caller, including failed
reads and ABI checks, is bounded without pointer ownership or future success. -/
theorem dynamic_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : Option (Option MlS))
    (first second third : ExpHOL 64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_encode_bytes") [first,second,third])).2.clock≤43314052496 := by
  apply ClockCost.call_arguments_current source destination (ofString "rlp_encode_bytes") [first,second,third] 43314052495
  intro values actual callee shape args called
  obtain ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩:=
    current_argument_entry source first second third values actual callee shape installed args called
  rw [bodyEq]
  exact body_domain_cost (callEntryStateHOLFinite source callee) dst src count installed domain d s n

/-- The fixed actual field length retains its smaller allowance even when
its pointer expressions fail to read or return the wrong shapes. -/
theorem dynamic_known_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : Option (Option MlS))
    (first second : ExpHOL 64) (length : Nat) (small : length+32<2^64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_encode_bytes")
      [first,second,.const (BitVec.ofNat 64 length)])).2.clock≤CopyAny.price length+21 := by
  apply ClockCost.call_arguments_current source destination (ofString "rlp_encode_bytes") [first,second,.const (BitVec.ofNat 64 length)] (CopyAny.price length+20)
  intro values actual callee shape args called
  obtain ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩:=
    current_argument_entry source first second (.const (BitVec.ofNat 64 length)) values actual callee shape installed args called
  have countEq : count=BitVec.ofNat 64 length:=by
    simpa only [eval,evalHOLExact,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using thirdRead.symm
  subst count
  rw [bodyEq]
  exact body_known_length_cost (callEntryStateHOLFinite source callee) dst src length small installed domain d s n

end InitECandidate.Solver.Input.CurrentRlp.BytesWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.current_argument_entry
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.dynamic_domain_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BytesWrite.dynamic_known_length_cost
