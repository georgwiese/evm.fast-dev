import InitECandidate.Solver.Input.HeaderEncoding.FieldRun

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem sizes_cons (field : Field) (rest : List Field) : sizes (field::rest)=maxSize field+sizes rest := by simp [sizes]
theorem costs_cons (field : Field) (rest : List Field) : costs (field::rest)=maxCost field+costs rest := by simp [costs]

/-- Compose the literal writer/advance sequence. Every step derives its real
arguments from preserved header memory and updates the natural output pointer. -/
theorem fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer old : BitVec 64)
    (items : List Field) (position : Nat) (context : Context source original header buffer) (codes : Codes source)
    (facts : ∀ field∈items,FieldFacts original header field) (positivePosition : 9≤position) (inside : position+sizes items≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (w : source.locals.lookup (ofString "w")=some (.val (.word old))) (enough : costs items≤source.clock) :
    ∃ target finalPosition last paid,position≤finalPosition ∧ finalPosition≤position+sizes items ∧ paid≤costs items ∧
      Context target original header buffer ∧ target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "p")=some (.val (.word (address buffer finalPosition))) ∧
      target.locals.lookup (ofString "w")=some (.val (.word last)) ∧
      (∀ name : String,ofString "p"≠ofString name→ ofString "w"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      (∀ continuation,evaluateHOLFiniteState source (fields items continuation)=evaluateHOLFiniteState target continuation) := by
  classical
  induction items generalizing source old position with
  | nil=>
    refine ⟨source,position,old,0,by omega,by simp [sizes],by simp [costs],context,by simp,p,w,by intros; rfl,?_⟩
    intro continuation
    rfl
  | cons field rest ih=>
    rw [sizes_cons] at inside
    rw [costs_cons] at enough
    obtain ⟨memory,encoded,fieldPaid,lower,upper,fieldBound,fieldRun,oldFrame⟩:=field_run source original header buffer old field position context codes
      (facts field (by simp)) positivePosition (by omega) p w (by omega)
    let next:=fieldPost source memory buffer position encoded fieldPaid
    have nextContext:=context.field_post source original memory header buffer position encoded fieldPaid oldFrame
    have nextCodes : Codes next:=⟨codes.u256Code,RlpWrite.U256Put.Codes.of_code source next rfl codes.u256Codes,codes.wordCode⟩
    have nextClock : next.clock=source.clock-fieldPaid:=rfl
    have nextState : next={source with locals:=next.locals,memory:=memory,clock:=source.clock-fieldPaid}:=rfl
    have nextLocals:=fieldPost_locals source memory buffer position encoded fieldPaid
    obtain ⟨target,finalPosition,last,tailPaid,positionLower,positionUpper,tailBound,targetContext,targetState,finalP,finalW,others,tailResume⟩:=
      ih next (BitVec.ofNat 64 encoded) (position+encoded) nextContext nextCodes
        (by intro field inside; exact facts field (List.mem_cons_of_mem _ inside)) (by omega) (by omega)
        nextLocals.1 nextLocals.2 (by omega)
    refine ⟨target,finalPosition,last,fieldPaid+tailPaid,by omega,?_,?_,targetContext,?_,finalP,finalW,?_,?_⟩
    · rw [sizes_cons]
      omega
    · rw [costs_cons]
      omega
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,memory:=target.memory,clock:=source.clock-fieldPaid-tailPaid} at targetState
      have subtract : source.clock-fieldPaid-tailPaid=source.clock-(fieldPaid+tailPaid) := by omega
      simpa only [subtract] using targetState
    · intro name pNe wNe
      exact (others name pNe wNe).trans (fieldPost_other source memory buffer position encoded fieldPaid name pNe wNe)
    · intro continuation
      have resumed:=(assemble_field source memory buffer field position encoded fieldPaid p fieldRun).2 (fields rest continuation)
      change evaluateHOLFiniteState source (fields (field::rest) continuation)=evaluateHOLFiniteState next (fields rest continuation) at resumed
      exact resumed.trans (tailResume continuation)

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.fields_execute
#print axioms InitECandidate.Solver.Input.HeaderEncoding.sizes_cons
#print axioms InitECandidate.Solver.Input.HeaderEncoding.costs_cons
