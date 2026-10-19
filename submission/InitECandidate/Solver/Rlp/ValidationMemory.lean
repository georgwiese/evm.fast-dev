import InitECandidate.Solver.Rlp.HeaderCallNormal

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact

structure Frame where
  pointer : BitVec 64
  resume : BitVec 64
  parentEnd : BitVec 64

def topOf : List Frame → BitVec 64 | [] => 0#64 | frame::_ => frame.pointer

/-- The original validator's real linked scratch records. Each saved
resume position is the current child end; its parent end bounds that resume.
The three mapped words contain exactly resume, parent end and prior top. -/
def Pending (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (cursor : Nat) (rootEnd : BitVec 64) :
    List Frame → BitVec 64 → Prop
  | [],ending => ending=rootEnd
  | frame::rest,ending =>
      ending=frame.resume ∧ frame.pointer≠0#64 ∧ cursor≤frame.pointer.toNat ∧ frame.pointer.toNat+24<2^64 ∧
      frame.resume.toNat≤frame.parentEnd.toNat ∧
      domain frame.pointer ∧ memory frame.pointer=.word frame.resume ∧
      domain (frame.pointer+8#64) ∧ memory (frame.pointer+8#64)=.word frame.parentEnd ∧
      domain (frame.pointer+16#64) ∧ memory (frame.pointer+16#64)=.word (topOf rest) ∧
      Pending memory domain cursor rootEnd rest frame.parentEnd

theorem Pending.end_le (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (cursor : Nat) (rootEnd : BitVec 64)
    (frames : List Frame) (ending : BitVec 64) (pending : Pending memory domain cursor rootEnd frames ending) : ending.toNat≤rootEnd.toNat := by
  induction frames generalizing ending with
  | nil => change ending=rootEnd at pending; rw [pending]
  | cons frame rest ih =>
    obtain ⟨sameEnd,active,lower,fits,ordered,mapped0,stored0,mapped8,stored8,mapped16,stored16,tail⟩ := pending
    rw [sameEnd]
    exact ordered.trans (ih frame.parentEnd tail)

/-- Fresh downward scratch writes below the previous cursor preserve every
older pending record, while allowing the current cursor to decrease. -/
theorem Pending.of_upper_agreement (memory memory' : BitVec 64 → HolWordLab 64) (domain domain' : BitVec 64 → Prop)
    (cursor nextCursor : Nat) (rootEnd : BitVec 64) (frames : List Frame) (ending : BitVec 64)
    (pending : Pending memory domain cursor rootEnd frames ending) (sameDomain : domain'=domain)
    (lowerCursor : nextCursor≤cursor) (agree : ∀ query,cursor≤query.toNat → memory' query=memory query) :
    Pending memory' domain' nextCursor rootEnd frames ending := by
  induction frames generalizing ending with
  | nil => exact pending
  | cons frame rest ih =>
    obtain ⟨sameEnd,active,lower,fits,ordered,mapped0,stored0,mapped8,stored8,mapped16,stored16,tail⟩ := pending
    have number8 : (frame.pointer+8#64).toNat=frame.pointer.toNat+8 := by
      rw [BitVec.toNat_add_of_lt (by change frame.pointer.toNat+8<2^64; omega)]
      rfl
    have number16 : (frame.pointer+16#64).toNat=frame.pointer.toNat+16 := by
      rw [BitVec.toNat_add_of_lt (by change frame.pointer.toNat+16<2^64; omega)]
      rfl
    refine ⟨sameEnd,active,lowerCursor.trans lower,fits,ordered,?_,?_,?_,?_,?_,?_,?_⟩
    · rwa [sameDomain]
    · exact (agree frame.pointer lower).trans stored0
    · rwa [sameDomain]
    · exact (agree (frame.pointer+8#64) (by rw [number8]; omega)).trans stored8
    · rwa [sameDomain]
    · exact (agree (frame.pointer+16#64) (by rw [number16]; omega)).trans stored16
    · exact ih frame.parentEnd tail

theorem Pending.empty_of_top_zero (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (cursor : Nat) (rootEnd : BitVec 64)
    (frames : List Frame) (ending : BitVec 64) (pending : Pending memory domain cursor rootEnd frames ending) (zero : topOf frames=0#64) :
    frames=[] ∧ ending=rootEnd := by
  cases frames with
  | nil => exact ⟨rfl,pending⟩
  | cons frame rest => exact (pending.2.1 zero).elim

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Pending.end_le
#print axioms InitECandidate.Solver.Rlp.Validation.Pending.of_upper_agreement
#print axioms InitECandidate.Solver.Rlp.Validation.Pending.empty_of_top_zero
