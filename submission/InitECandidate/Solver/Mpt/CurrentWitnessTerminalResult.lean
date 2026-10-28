import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack

/-- A real terminal decoder result names zero or a fresh persistent node.
These numeric bounds also protect earlier input from later cache metadata
writes; no arbitrary returned word is treated as a fresh pointer. -/
def TerminalResult (heap : BitVec 64) (value : ValueHOL 64) : Prop :=
  ∃ node,value=.rStruct [.val (.word 0#64),.val (.word node)] ∧
    (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016)

theorem TerminalResult.empty (heap : BitVec 64) : TerminalResult heap (.rStruct [.val (.word 0#64),.val (.word 0#64)]) :=
  ⟨0#64,rfl,Or.inl rfl⟩

theorem TerminalResult.mono (heap next : BitVec 64) (grows : heap.toNat≤next.toNat)
    {value : ValueHOL 64} (result : TerminalResult next value) : TerminalResult heap value := by
  obtain ⟨node,same,zero|⟨lower,upper⟩⟩:=result
  · exact ⟨node,same,Or.inl zero⟩
  · exact ⟨node,same,Or.inr ⟨Nat.le_trans grows lower,upper⟩⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.TerminalResult.empty
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.TerminalResult.mono
