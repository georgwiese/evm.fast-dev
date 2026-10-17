import InitECandidate.Solver.Input.HeaderEncoding.Reads

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fieldPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : Memory) (buffer : BitVec 64) (position encoded paid : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind {source with memory:=memory,clock:=source.clock-paid} "w" (BitVec.ofNat 64 encoded)) "p" (address buffer (position+encoded))

/-- Assemble a real existing-w writer call with the actual following p update,
both alone and in its literal right-nested continuation. -/
theorem assemble_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : Memory) (buffer : BitVec 64)
    (field : Field) (position encoded paid : Nat)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (run : evaluateHOLFiniteState source (call field)=
      (none,bind {source with memory:=memory,clock:=source.clock-paid} "w" (BitVec.ofNat 64 encoded))) :
    evaluateHOLFiniteState source (.seq (call field) advance)=(none,fieldPost source memory buffer position encoded paid) ∧
    (∀ continuation,evaluateHOLFiniteState source (fields [field] continuation)=
      evaluateHOLFiniteState (fieldPost source memory buffer position encoded paid) continuation) := by
  classical
  let entered:=bind {source with memory:=memory,clock:=source.clock-paid} "w" (BitVec.ofNat 64 encoded)
  have pEntered : entered.locals.lookup (ofString "p")=some (.val (.word (address buffer position))):=
    (bind_lookup_other _ "w" "p" _ (by decide)).trans p
  have wEntered : entered.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=bind_lookup_same _ _ _
  have addRead : eval entered advanceExpression=some (.val (.word (address buffer (position+encoded)))) := by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,pEntered,wEntered,valueIsWord,valueWord,wordOpHOL,wordOp,
      address,BitVec.ofNat_add,BitVec.add_assoc]
  have advanceRun:=WitnessRadix.StateSteps.assign_execute entered "p" advanceExpression _ _ pEntered addRead
  change evaluateHOLFiniteState entered advance=(none,fieldPost source memory buffer position encoded paid) at advanceRun
  constructor
  · rw [WitnessRadix.StateSteps.next_sequence source entered _ _ run (by change source.clock-paid≤source.clock; omega)]
    exact advanceRun
  · intro continuation
    rw [fields,fields,WitnessRadix.StateSteps.next_sequence source entered _ _ run (by change source.clock-paid≤source.clock; omega),
      WitnessRadix.StateSteps.next_sequence entered (fieldPost source memory buffer position encoded paid) _ _ advanceRun (Nat.le_refl _)]

theorem fieldPost_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : Memory) (buffer : BitVec 64) (position encoded paid : Nat) :
    (fieldPost source memory buffer position encoded paid).locals.lookup (ofString "p")=some (.val (.word (address buffer (position+encoded)))) ∧
      (fieldPost source memory buffer position encoded paid).locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))) :=
  ⟨bind_lookup_same _ _ _,(bind_lookup_other _ "p" "w" _ (by decide)).trans (bind_lookup_same _ _ _)⟩

theorem fieldPost_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : Memory) (buffer : BitVec 64) (position encoded paid : Nat) (name : String)
    (pNe : ofString "p"≠ofString name) (wNe : ofString "w"≠ofString name) :
    (fieldPost source memory buffer position encoded paid).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "p" name _ pNe).trans (bind_lookup_other _ "w" name _ wNe)

theorem Context.field_post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original memory : Memory) (header buffer : BitVec 64)
    (position encoded paid : Nat) (context : Context source original header buffer) (frame : OldMemory memory original buffer) :
    Context (fieldPost source memory buffer position encoded paid) original header buffer := by
  exact ⟨context.geometry,context.domain,frame,
    (fieldPost_other source memory buffer position encoded paid "h" (by decide) (by decide)).trans context.headerLocal,context.heap⟩

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.assemble_field
#print axioms InitECandidate.Solver.Input.HeaderEncoding.fieldPost_locals
#print axioms InitECandidate.Solver.Input.HeaderEncoding.fieldPost_other
#print axioms InitECandidate.Solver.Input.HeaderEncoding.Context.field_post
