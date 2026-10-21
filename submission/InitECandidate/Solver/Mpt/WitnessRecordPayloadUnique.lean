import InitECandidate.Solver.Mpt.WitnessRecordView

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Descriptions of the same genuine physical record agree on its stage
payload and counters. No uniqueness of RLP item lists is assumed. -/
theorem View.payload_unique (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db : BitVec 64)
    (first second : Description) (left : View source record db first) (right : View source record db second) : first.payload=second.payload := by
  have stage : first.payload.stage=second.payload.stage := HolWordLab.word.inj
    ((left.stage source record db first).symm.trans (right.stage source record db second))
  cases firstPayload : first.payload with
  | extension nibbles length=>
    cases secondPayload : second.payload with
    | extension nibbles2 length2=>
      have sameNibbles : nibbles=nibbles2 := HolWordLab.word.inj
        ((left.cells (64,nibbles) (by simp [Description.cells,firstPayload])).symm.trans (right.cells (64,nibbles2) (by simp [Description.cells,secondPayload])))
      have sameLength : length=length2 := HolWordLab.word.inj
        ((left.cells (72,length) (by simp [Description.cells,firstPayload])).symm.trans (right.cells (72,length2) (by simp [Description.cells,secondPayload])))
      rw [sameNibbles,sameLength]
    | branch node index occupied=>simp [firstPayload,secondPayload,Payload.stage] at stage
  | branch node index occupied=>
    cases secondPayload : second.payload with
    | extension nibbles length=>simp [firstPayload,secondPayload,Payload.stage] at stage
    | branch node2 index2 occupied2=>
      have sameNode : node=node2 := HolWordLab.word.inj
        ((left.cells (16,node) (by simp [Description.cells,firstPayload])).symm.trans (right.cells (16,node2) (by simp [Description.cells,secondPayload])))
      have indexWord : BitVec.ofNat 64 index.val=BitVec.ofNat 64 index2.val := HolWordLab.word.inj
        ((left.cells (32,BitVec.ofNat 64 index.val) (by simp [Description.cells,firstPayload])).symm.trans
          (right.cells (32,BitVec.ofNat 64 index2.val) (by simp [Description.cells,secondPayload])))
      have occupiedWord : BitVec.ofNat 64 occupied.val=BitVec.ofNat 64 occupied2.val := HolWordLab.word.inj
        ((left.cells (40,BitVec.ofNat 64 occupied.val) (by simp [Description.cells,firstPayload])).symm.trans
          (right.cells (40,BitVec.ofNat 64 occupied2.val) (by simp [Description.cells,secondPayload])))
      have sameIndex : index=index2 := Fin.ext (by
        have number:=congrArg BitVec.toNat indexWord
        rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=index.isLt; omega),Nat.mod_eq_of_lt (by have bound:=index2.isLt; omega)] at number
        exact number)
      have sameOccupied : occupied=occupied2 := Fin.ext (by
        have number:=congrArg BitVec.toNat occupiedWord
        rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=occupied.isLt; omega),Nat.mod_eq_of_lt (by have bound:=occupied2.isLt; omega)] at number
        exact number)
      rw [sameNode,sameIndex,sameOccupied]

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.payload_unique
