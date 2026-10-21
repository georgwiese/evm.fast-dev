import InitECandidate.Solver.Mpt.CompactToNibblesInitial
import InitECandidate.Solver.Input.DeclarationTrace

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Observe the real first byte. Failure stops at zero source ticks;
successful declaration retains the actual byte, suffix and local restore. -/
theorem byte_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterGuard=(outcome,post)) :
    source.clock-post.clock≤0 ∨ ∃ byte : UInt8,∃ inner,
      evaluateHOLFiniteState (QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)) afterByte=(outcome,inner) ∧
      post=restore source "c0" inner := by
  rw [byte_shape] at run
  rcases Input.declaration_trace source post "c0" .one (.loadByte (localVar "p")) afterByte outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=reached
    cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be pointer with
    | none=>
      have bad : eval source (.loadByte (localVar "p"))=none:=by simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
      rw [bad] at read
      cases read
    | some byte=>
      have actual : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 byte.toNat))):=by
        simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
      have same : declared=.val (.word (BitVec.ofNat 64 byte.toNat)):=Option.some.inj (read.symm.trans actual)
      subst declared
      exact Or.inr ⟨byte,inner,continued,endpoint⟩

/-- At every actual allocation entry the byte and flag calculations have
really run. No mapped input, future room or successful allocation is assumed. -/
theorem allocation_entry_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterGuard=(outcome,post)) :
    source.clock-post.clock≤0 ∨ ∃ byte : UInt8,∃ restoreStack inner,
      let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
      ProgramPrefix.Executes byteState initialActions (prepared byteState (BitVec.ofNat 64 byte.toNat)) restoreStack ∧
      evaluateHOLFiniteState (prepared byteState (BitVec.ofNat 64 byte.toNat)) allocationCall=(outcome,inner) ∧
      post=restore source "c0" (restoreStack inner) ∧ post.clock=inner.clock := by
  rcases byte_trace source post pointer pointerCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨byte,innerByte,continued,endpoint⟩:=reached
    let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
    obtain ⟨restoreStack,inner,setup,allocation,innerEq,clock⟩:=initial_trace byteState innerByte (BitVec.ofNat 64 byte.toNat) (bind_lookup_same _ _ _) outcome continued
    exact Or.inr ⟨byte,restoreStack,inner,setup,allocation,by rw [endpoint,innerEq],by rw [endpoint]; exact clock⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.byte_trace
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.allocation_entry_trace
