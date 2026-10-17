import InitECandidate.Solver.WitnessRadix.Keccak256OutWords

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure OutMapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) : Prop where
  copy : CopyContext.Mapped source stp out 32
  stateWords : ∀ offset<32,offset%8=0 → source.memaddrs (byteAddress stp offset)
  outputWords : out &&& 7#64=0#64 → ∀ offset<32,offset%8=0 → source.memaddrs (byteAddress out offset)

theorem output_alignment_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    eval source outAlignment=some (.val (.word (if out &&& 7#64=0#64 then 1#64 else 0#64))) := by
  by_cases mask : out &&& 7#64=0#64
  all_goals simp [eval,outAlignment,localVar,evalHOLExact,evalListHOLExact,toExact,outLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,mask]

/-- Both literal digest-output paths, including their real stores or memcpy
call. No separate successful output execution is assumed. -/
theorem output_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64)
    (stpLocal : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (mapped : OutMapped source stp out)
    (code : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one)) (enough : 33≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source outProgram=(none,output) ∧ output.locals=source.locals ∧
      output.clock≤source.clock ∧ source.clock-33≤output.clock ∧ KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,CopyGeneral.Away out query 32 → output.memory query=source.memory query := by
  classical
  have read := output_alignment_read source out outLocal
  simp only [eval] at read
  by_cases mask : out &&& 7#64=0#64
  · have run := out_words_execute source stp out stpLocal outLocal mapped.stateWords (mapped.outputWords mask)
    let output := {source with memory := outMemoryMany source.memory stp out [0,8,16,24]}
    refine ⟨output,?_,rfl,Nat.le_refl _,by change source.clock-33≤source.clock; omega,rfl,?_⟩
    · rw [outProgram,evaluateHOLFiniteState_ite,read]
      simpa [mask] using run
    · intro query away
      apply out_memory_away
      intro offset member
      simp at member
      rcases member with rfl|rfl|rfl|rfl <;> exact (away _ (by decide)).1
  · have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [localVar "out",localVar "stp",.const 32#64]=some (CopyGeneral.values out stp 32) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,outLocal,stpLocal,CopyGeneral.values]
    have bound := CopyGeneral.cost_le stp out 32
    have run := CopyGeneral.call_execute source [localVar "out",localVar "stp",.const 32#64] stp out 32 args code mapped.copy (by decide) (by omega)
    refine ⟨CopyGeneral.callState source stp out 32,?_,rfl,?_,?_,?_,?_⟩
    · rw [outProgram,evaluateHOLFiniteState_ite,read]
      simpa [mask,outCopy] using run
    · change source.clock-(CopyGeneral.cost stp out 32+1)≤source.clock
      omega
    · change source.clock-33≤source.clock-(CopyGeneral.cost stp out 32+1)
      omega
    · exact KeccakAbsorb.hashControl_of_control source _ (CopyGeneral.call_control source stp out 32)
    · intro query away
      exact CopyGeneral.call_memory_away source stp out query 32 away

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.output_alignment_read
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.output_execute
