import InitECandidate.Solver.Input.CurrentRlp.HeaderFields
import InitECandidate.Solver.Input.HeaderEncoding.Suffix

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

set_option maxRecDepth 100000

theorem codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : Codes source := by
  exact ⟨by simpa only [WideWrite.current_body] using WideWrite.original_code source.code installed,
    WideWrite.helper_codes source installed,by simpa only [WordWrite.current_body] using WordWrite.original_code source.code installed⟩

theorem tail_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : TailCodes source := by
  constructor
  · apply Code.installed_as source.code installed .listLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_list_header_len,RlpLength.ListHeader.formals,RlpLength.ListHeader.body,Guest.guestFn_rlp_list_header_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .headerLength
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_header_len,RlpLength.Header.formals,RlpLength.Header.body,Guest.guestFn_rlp_header_len,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
  · apply Code.installed_as source.code installed .writeList
    simp only [Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
      Guest.Software.guestFn_rlp_encode_list_header,RlpWrite.ListWrite.formals,RlpWrite.ListWrite.body,Guest.guestFn_rlp_encode_list_header,
      paramToHOL,shapeToHOL,List.map_cons,List.map_nil]

/-- All suffix outcomes obey the source allowance, at the actual physical
header and output position supplied by the preceding writer prefix. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source suffix).2.clock≤31 := by
  by_cases funded : 31≤source.clock
  · obtain ⟨target,start,encoded,paid,positive,size,bound,number,run,frame,memory,arena⟩:=suffix_execute_bounded source original header buffer position
      context (codes source installed) (tail_codes source installed) lower upper p buf funded
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run]
    change source.clock-target.clock≤31
    omega
  · omega

/-- The genuine normal suffix return has a mapped encoded output span,
length at most916, and preserves the old header/input memory and metadata. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (lower : 9≤position) (upper : position≤916)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source suffix=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  let padded:={source with clock:=source.clock+31}
  have paddedContext : Context padded original header buffer:=
    ⟨context.geometry,context.domain,context.oldMemory,context.headerLocal,context.heap⟩
  obtain ⟨post,start,encoded,paid,positive,size,bound,number,run,frame,memory,arena⟩:=suffix_execute_bounded padded original header buffer position
    paddedContext (codes padded installed) (tail_codes padded installed) lower upper p buf (by change 31≤source.clock+31; omega)
  have lifted:=panPropsEvaluateAddClockEq suffix source (some (.returned value)) target 31 ⟨returned,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+31}=post at endpoint
  rw [←endpoint] at frame memory
  have metadata:=congrArg MemoryMetadata.erase frame
  exact ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.tail_codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderSuffix.normal
