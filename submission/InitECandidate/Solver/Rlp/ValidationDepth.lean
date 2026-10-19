import InitECandidate.Solver.Rlp.ValidationMemory
import InitECandidate.Solver.Rlp.ValidationRank

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real saved parent/link words make the finite pending depth unique,
even though the invariant's list is only a proof witness. -/
theorem Pending.depth_unique (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (cursor : Nat) (rootEnd : BitVec 64)
    (frames other : List Frame) (ending : BitVec 64)
    (pending : Pending memory domain cursor rootEnd frames ending) (otherPending : Pending memory domain cursor rootEnd other ending)
    (sameTop : topOf frames=topOf other) : frames.length=other.length := by
  induction frames generalizing other ending with
  | nil =>
    cases other with
    | nil => rfl
    | cons frame rest => exact (otherPending.2.1 sameTop.symm).elim
  | cons frame rest ih =>
    cases other with
    | nil => exact (pending.2.1 sameTop).elim
    | cons next tail =>
      obtain ⟨sameEnd,active,lower,fits,ordered,mapped0,stored0,mapped8,stored8,mapped16,stored16,pendingTail⟩ := pending
      obtain ⟨otherEnd,otherActive,otherLower,otherFits,otherOrdered,otherMapped0,otherStored0,otherMapped8,otherStored8,otherMapped16,otherStored16,otherTail⟩ := otherPending
      have pointers : frame.pointer=next.pointer := sameTop
      have parentWords : HolWordLab.word frame.parentEnd=HolWordLab.word next.parentEnd :=
        stored8.symm.trans (by rw [pointers]; exact otherStored8)
      have parentEq : frame.parentEnd=next.parentEnd := HolWordLab.word.inj parentWords
      have previousWords : HolWordLab.word (topOf rest)=HolWordLab.word (topOf tail) :=
        stored16.symm.trans (by rw [pointers]; exact otherStored16)
      have previousEq : topOf rest=topOf tail := HolWordLab.word.inj previousWords
      have tailModel : Pending memory domain cursor rootEnd tail frame.parentEnd := by rw [parentEq]; exact otherTail
      have lengths := ih tail frame.parentEnd pendingTail tailModel previousEq
      simp only [List.length_cons,lengths]

noncomputable def physicalDepth (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (cursor : Nat) (rootEnd ending top : BitVec 64) : Nat := by
  classical
  exact if witness : ∃ frames,Pending memory domain cursor rootEnd frames ending ∧ topOf frames=top
    then (Classical.choose witness).length else 0

theorem physicalDepth_eq (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (cursor : Nat)
    (rootEnd ending top : BitVec 64) (frames : List Frame)
    (pending : Pending memory domain cursor rootEnd frames ending) (sameTop : topOf frames=top) :
    physicalDepth memory domain cursor rootEnd ending top=frames.length := by
  classical
  have witness : ∃ frames,Pending memory domain cursor rootEnd frames ending ∧ topOf frames=top := ⟨frames,pending,sameTop⟩
  unfold physicalDepth
  rw [dif_pos witness]
  have chosen := Classical.choose_spec witness
  exact Pending.depth_unique memory domain cursor rootEnd (Classical.choose witness) frames ending chosen.1 pending (chosen.2.trans sameTop.symm)

def localWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64 :=
  match source.locals.lookup (ofString name) with | some (.val (.word word)) => word | _ => 0#64
def globalWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64 :=
  match source.globals.lookup (ofString name) with | some (.val (.word word)) => word | _ => 0#64
noncomputable def currentDepth (rootEnd : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  physicalDepth source.memory source.memaddrs (globalWord source "scratch_ptr").toNat rootEnd (localWord source "end") (localWord source "top")
noncomputable def currentRank (rootEnd : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  rank rootEnd (localWord source "pos") (currentDepth rootEnd source) (decide (localWord source "go"≠0#64))

theorem current_rank_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rootEnd cursor position ending go : BitVec 64) (frames : List Frame)
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word (topOf frames))))
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go)))
    (pending : Pending source.memory source.memaddrs cursor.toNat rootEnd frames ending) :
    currentRank rootEnd source=rank rootEnd position frames.length (decide (go≠0#64)) := by
  unfold currentRank currentDepth
  simp only [globalWord,localWord,cursorCell,positionCell,endCell,topCell,goCell]
  rw [physicalDepth_eq source.memory source.memaddrs cursor.toNat rootEnd ending (topOf frames) frames pending rfl]

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Pending.depth_unique
#print axioms InitECandidate.Solver.Rlp.Validation.physicalDepth_eq
#print axioms InitECandidate.Solver.Rlp.Validation.current_rank_eq
