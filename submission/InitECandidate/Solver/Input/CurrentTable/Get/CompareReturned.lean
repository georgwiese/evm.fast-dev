import InitECandidate.Solver.Input.CurrentTable.Get.ValueRead
import InitECandidate.Solver.Input.ReturnFacts
import InitECandidate.Solver.Input.PureDecision

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def absentValue : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64)]
def presentValue (value : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word 1#64),.val (.word value)]
def Result (ValueOf : BitVec 64 → Prop) (value : ValueHOL 64) : Prop :=
  value=absentValue ∨ ∃ member,value=presentValue member ∧ ValueOf member

theorem absent_returned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ValueOf : BitVec 64 → Prop) :
    ReturnFacts.Returns source absent (Result ValueOf) :=
  ReturnFacts.returned source _ absentValue (Result ValueOf) rfl (Or.inl rfl)

/-- Any real comparison continuation either reports absence or returns a
value physically stored at the actual selected leaf. No byte-equality or
future successful-read hypothesis is needed for this membership contract. -/
theorem after_compare_returned {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (member : valid leaf) (marked : bits leaf=256) :
    ReturnFacts.Returns source afterCompare (Result ValueOf) := by
  apply ReturnFacts.sequence source compareGuard _ (Result ValueOf)
  · exact ReturnFacts.conditional source _ _ _ (Result ValueOf) (absent_returned source ValueOf) (ReturnFacts.skip source _)
  · intro middle normal
    have decision : PureDecision compareGuard := .ite _ (.returned _) .skip
    have same := decision.summary source
    rw [normal] at same
    have middleEq : middle=source := same.1 rfl
    subst middle
    obtain ⟨value,loaded,validValue⟩ := leaf_value_read image tableCell leafCell member marked
    have read : eval source (.rstruct [.const 1#64,valueRead])=some (presentValue value) := by
      simp only [eval] at loaded ⊢
      rw [evalHOLExact]
      simp only [evalListHOLExact,loaded]
      rfl
    exact ReturnFacts.returned source _ (presentValue value) (Result ValueOf) read (Or.inr ⟨value,rfl,validValue⟩)

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.after_compare_returned
