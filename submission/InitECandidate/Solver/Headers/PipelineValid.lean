import InitECandidate.Solver.Headers.PipelineProgram

namespace InitECandidate.Solver.Headers.Pipeline
open Flapjack

/-- Static obligations of the exact original pipeline: real selected rows,
checked local shapes, active store values, and bounded header footprints. -/
def Valid (count : Nat) (current : BitVec 64) (active : List Slot) : Code→Prop
  | .done | .returned=>True
  | .store offset value rest=>value.Ready active ∧ offset+8*value.words≤248 ∧ Valid count current active rest
  | .declare slot kind index _ rest=>kind.resultShape=slot.shape ∧ index<count ∧ Valid count current (slot::active) rest
  | .assign slot kind index _ rest=>kind.resultShape=slot.shape ∧ index<count ∧ slot∈active ∧ Valid count current active rest
  | .guard _ _ _ rest=>Valid count current active rest
  | .choose yes no rest=>(if current=0#64 then Valid count current active no else Valid count current active yes) ∧ Valid count current active rest

set_option maxRecDepth 10000 in
theorem fields_valid (current : BitVec 64) (count : Nat)
    (branch : (current=0#64 ∧ count=21) ∨ (current=1#64 ∧ count=23)) : Valid count current [] fields := by
  rcases branch with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Valid,fields,afterF,afterD,afterW,afterTsf,afterEx,afterBg,final,bytesSet,wordSet,u256Set,uintSet,StoreValue.Ready,StoreValue.words,Slot.words,Slot.shape,Helper.Kind.resultShape,Field.Kind.resultShape,Input.ScalarPair.tupleShape,Input.RlpWrite.U256Value.tupleShape]

def rowBytes (items : List Rlp.ListItem) (index : Nat) : Nat := ((items[index]?).map fun item=>item.total.toNat).getD 0

/-- Only source call/loop ticks. The branch is the actual original21/23
bit, and each helper is charged using its own selected encoded row. -/
def price (items : List Rlp.ListItem) (current : BitVec 64) : Code→Nat
  | .done | .returned=>0
  | .store _ _ rest | .guard _ _ _ rest=>price items current rest
  | .declare _ kind index _ rest | .assign _ kind index _ rest=>kind.bodyPrice (rowBytes items index)+1+price items current rest
  | .choose yes no rest=>(if current=0#64 then price items current no else price items current yes)+price items current rest

theorem rowBytes_selected (items : List Rlp.ListItem) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    rowBytes items index=item.total.toNat := by simp [rowBytes,selected]

end InitECandidate.Solver.Headers.Pipeline

#print axioms InitECandidate.Solver.Headers.Pipeline.fields_valid
#print axioms InitECandidate.Solver.Headers.Pipeline.rowBytes_selected
