import InitECandidate.Solver.WitnessRadix.ConstructorHashFrame

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

def setKey (keyFor : BitVec 64 → ByteKeys.Key) (index : Nat) (key : ByteKeys.Key) : BitVec 64 → ByteKeys.Key :=
  fun ordinal => if ordinal=BitVec.ofNat 64 index then key else keyFor ordinal

theorem setKey_current (keyFor : BitVec 64 → ByteKeys.Key) (index : Nat) (key : ByteKeys.Key) :
    setKey keyFor index key (BitVec.ofNat 64 index)=key := if_pos rfl

theorem setKey_earlier (layout : Layout) (valid : Valid layout) (keyFor : BitVec 64 → ByteKeys.Key) (index : Nat) (key : ByteKeys.Key)
    (inside : index<layout.count) (old : Nat) (earlier : old<index) : setKey keyFor index key (BitVec.ofNat 64 old)=keyFor (BitVec.ofNat 64 old) := by
  have count := count_small layout valid
  have different : (BitVec.ofNat 64 old)≠BitVec.ofNat 64 index := by
    intro same
    have h := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at h
    omega
  exact if_neg different

theorem Prefix.rekey_current {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (index : Nat) (key : ByteKeys.Key) (inside : index<layout.count)
    (prefixData : Prefix source layout keyFor index) : Prefix source layout (setKey keyFor index key) index := by
  refine ⟨prefixData.recordWords,?_,prefixData.ordinalWords⟩
  intro old earlier
  rw [setKey_earlier layout valid keyFor index key inside old earlier]
  exact prefixData.hashViews old earlier

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.setKey_current
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.setKey_earlier
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.Prefix.rekey_current
