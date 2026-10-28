import InitECandidate.Solver.Mpt.CompactToNibblesByteTrace
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal compact decode has passed the empty guard, read its
real first byte and reached the actual allocator after all flag declarations.
No successful allocation or returned pointer is supplied as a premise. -/
theorem normal_allocation_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    1≤length ∧ ∃ byte : UInt8,∃ restoreStack inner,
      let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
      ProgramPrefix.Executes byteState initialActions (prepared byteState (BitVec.ofNat 64 byte.toNat)) restoreStack ∧
      evaluateHOLFiniteState (prepared byteState (BitVec.ofNat 64 byte.toNat)) allocationCall=(some (.returned value),inner) ∧
      target=restore source "c0" (restoreStack inner) ∧ target.clock=inner.clock := by
  rw [body_shape] at normal
  have guardSafe : Input.LocalPrefix (ofString "n") (.ite zeroTest fail .skip):=
    .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,guardRun,continued,localFrame⟩:=guardSafe.normal_continue source target afterGuard value normal
  obtain ⟨test,middleEq⟩:=Fail.guard_normal source middle zeroTest [.const 5#64] installed guardRun
  have positive : 1≤length:=by
    by_cases positive : 1≤length
    · exact positive
    · exfalso
      have zero : length=0:=by omega
      have actual : eval source zeroTest=some (.val (.word 1#64)):=by
        simp [eval,zeroTest,evalHOLExact,localVar,toExact,lengthCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have impossible : (1#64 : BitVec 64)=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans test
      exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  rw [middleEq,byte_shape] at continued
  obtain ⟨declared,innerByte,read,checked,byteRun,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "c0" .one (.loadByte (localVar "p")) afterByte value continued
  cases loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun query=>Classical.propDecidable (source.memaddrs query)) source.be pointer with
  | none=>
    have bad : eval source (.loadByte (localVar "p"))=none:=by simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
    rw [bad] at read
    cases read
  | some byte=>
    have actual : eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 byte.toNat))):=by simp [eval,localVar,evalHOLExact,toExact,pointerCell,loaded]
    have same : declared=.val (.word (BitVec.ofNat 64 byte.toNat)):=Option.some.inj (read.symm.trans actual)
    subst declared
    let byteState:=QueryBranch.bind source "c0" (BitVec.ofNat 64 byte.toNat)
    obtain ⟨restoreStack,inner,setup,allocation,innerEq,clock⟩:=initial_trace byteState innerByte (BitVec.ofNat 64 byte.toNat) (bind_lookup_same _ _ _) (some (.returned value)) byteRun
    exact ⟨positive,byte,restoreStack,inner,setup,allocation,by rw [endpoint,innerEq],by rw [endpoint]; exact clock⟩

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.normal_allocation_entry
