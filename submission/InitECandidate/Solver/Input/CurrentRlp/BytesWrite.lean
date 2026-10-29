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
