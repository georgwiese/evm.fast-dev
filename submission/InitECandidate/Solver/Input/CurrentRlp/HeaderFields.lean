import InitECandidate.Solver.Input.CurrentRlp.FieldWrite
import InitECandidate.Solver.Input.HeaderEncoding.FirstWideProgram
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open HeaderEncoding

/-- The actual writer prefix retains the earlier header, heap and every
caller local except its current output pointer and field result. -/
structure Positioned (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (position : Nat) : Prop where
  context : Context current original header buffer
  metadata : MemoryMetadata.erase current=MemoryMetadata.erase source
  pointer : current.locals.lookup (ofString "p")=some (.val (.word (address buffer position)))
  locals : ∀ name : String,ofString "p"≠ofString name→ofString "w"≠ofString name→
    current.locals.lookup (ofString name)=source.locals.lookup (ofString name)

theorem Positioned.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (position : Nat) (context : Context source original header buffer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position)))) :
    Positioned source source original header buffer position:=⟨context,rfl,p,by intros; rfl⟩

theorem Positioned.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {original : Memory}
    {header buffer : BitVec 64} {first second : Nat}
    (front : Positioned source middle original header buffer first) (back : Positioned middle target original header buffer second) :
    Positioned source target original header buffer second:=
  ⟨back.context,back.metadata.trans front.metadata,back.pointer,fun name pNe wNe=>(back.locals name pNe wNe).trans (front.locals name pNe wNe)⟩

theorem fields_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (field : Field) (rest : List Field) (tail : ProgHOL 64) :
    evaluateHOLFiniteState source (fields (field::rest) tail)=
      evaluateHOLFiniteState source (.seq (.seq (call field) advance) (fields rest tail)) := by
  simp only [fields,evaluateHOLFiniteState_seq_line780]
  generalize evaluateHOLFiniteState source (call field)=output
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>rfl
  | some result=>rfl

theorem step_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (field : Field) (ready : FieldWrite.Prepared source original header buffer field) :
    source.clock-(evaluateHOLFiniteState source (.seq (call field) advance)).2.clock≤maxCost field := by
  have price:=ClockCost.sequence_current source (call field) advance (maxCost field) 0
    (ready.call_cost source original header buffer field) (ClockCost.assign source.code (ofString "p") advanceExpression)
  simpa only [Nat.add_zero] using price

/-- Compose field prices only at actually reached states. The callback is
used after the real normal writer-and-pointer prefix, never for an aborted
field. No successful future call or persistent temporary room is assumed. -/
theorem fields_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (items : List Field) (position : Nat) (context : Context source original header buffer)
    (installed : OriginalCode.Installed source.code) (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈items,FieldFacts original header field) (inside : position+sizes items≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (tail : ProgHOL 64) (price : Nat)
    (back : ∀ current finalPosition,position≤finalPosition→finalPosition≤position+sizes items→
      Positioned source current original header buffer finalPosition→
      current.clock-(evaluateHOLFiniteState current tail).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (fields items tail)).2.clock≤costs items+price := by
  induction items generalizing source position with
  | nil=>
    have next:=back source position (by omega) (by simp [sizes]) (Positioned.refl source original header buffer position context p)
    simpa only [fields,costs,List.map_nil,List.sum_nil,Nat.zero_add] using next
  | cons field rest ih=>
    have sizeSum : sizes (field::rest)=maxSize field+sizes rest:=by simp [sizes]
    have costSum : costs (field::rest)=maxCost field+costs rest:=by simp [costs]
    have ready:=FieldWrite.prepare source original header buffer field position context installed bounded (facts field (by simp)) (by omega) p
    have priced:=ClockCost.sequence_reached_current source (.seq (call field) advance) (fields rest tail) (maxCost field) (costs rest+price)
      (step_cost source original header buffer field ready) (by
        intro middle actual
        obtain ⟨encoded,positive,upper,nextContext,metadata,nextP,nextW,others⟩:=
          ready.step_normal source middle original header buffer field position context p actual
        have reached : Positioned source middle original header buffer (position+encoded):=⟨nextContext,metadata,nextP,others⟩
        have nextInstalled : OriginalCode.Installed middle.code:=by rw [MemoryMetadata.code metadata]; exact installed
        apply ih middle (position+encoded) nextContext nextInstalled
          (by intro item member; exact facts item (List.mem_cons_of_mem _ member)) (by omega) nextP
        intro target finalPosition lower finalUpper later
        exact back target finalPosition (by omega) (by omega) (reached.trans later))
    rw [fields_step]
    rw [costSum]
    omega

/-- A returning continuation is reached only after the real normal field
prefix, with a bounded natural output pointer and retained physical image. -/
theorem fields_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (items : List Field) (position : Nat) (context : Context source original header buffer)
    (installed : OriginalCode.Installed source.code) (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈items,FieldFacts original header field) (inside : position+sizes items≤1024)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (tail : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (fields items tail)=(some (.returned value),post)) :
    ∃ current finalPosition,position≤finalPosition ∧ finalPosition≤position+sizes items ∧
      Positioned source current original header buffer finalPosition ∧
      evaluateHOLFiniteState current tail=(some (.returned value),post) := by
  induction items generalizing source position with
  | nil=>exact ⟨source,position,by omega,by simp [sizes],Positioned.refl source original header buffer position context p,normal⟩
  | cons field rest ih=>
    rw [fields_step] at normal
    have advanceNever : NoReturn.Never advance:=by
      intro F source value
      have localOnly : LocalPrefix (ofString "_") advance:=.assign _ _ (by decide)
      exact (localOnly.summary source).2 value
    obtain ⟨middle,actual,remaining⟩:=sequence_returned source post (.seq (call field) advance) (fields rest tail) value
      (NoReturn.sequence _ _ (field_never field) advanceNever source) normal
    have sizeSum : sizes (field::rest)=maxSize field+sizes rest:=by simp [sizes]
    have ready:=FieldWrite.prepare source original header buffer field position context installed bounded (facts field (by simp)) (by omega) p
    obtain ⟨encoded,positive,upper,nextContext,metadata,nextP,nextW,others⟩:=
      ready.step_normal source middle original header buffer field position context p actual
    have reached : Positioned source middle original header buffer (position+encoded):=⟨nextContext,metadata,nextP,others⟩
    have nextInstalled : OriginalCode.Installed middle.code:=by rw [MemoryMetadata.code metadata]; exact installed
    obtain ⟨current,finalPosition,lower,finalUpper,later,run⟩:=ih middle (position+encoded) nextContext nextInstalled
      (by intro item member; exact facts item (List.mem_cons_of_mem _ member)) (by omega) nextP remaining
    exact ⟨current,finalPosition,by omega,by omega,reached.trans later,run⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderFields

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.Positioned.refl
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.Positioned.trans
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.fields_step
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.step_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.fields_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFields.fields_returned
