import InitECandidate.Solver.Input.PContainerProgram

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem bit_step_summary (key : MlS) (different : key≠ofString "i") : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key bitStep source := by
  intro source
  rw [body_shape.2.2.2.2.2.2.2.2.1]
  exact local_summary_sequence key _ _ (byte_store_local key _ _) (LocalPrefix.assign _ _ different).summary_full source

theorem bit_step_quiet (code) : QuietClock.Preserves code bitStep := by
  rw [body_shape.2.2.2.2.2.2.2.2.1]
  exact QuietClock.sequence code _ _ (QuietClock.store_byte code _ _) (QuietClock.assign code _ _)

theorem bit_model (code) (n : Nat) (short : n<32) : ZeroShort.Model code test bitStep 1 n := by
  refine ⟨by decide,short,?_,?_,bit_step_summary (ofString "n") (by decide),bit_step_quiet code⟩
  · intro source index inside indexLocal lengthLocal
    have iNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have nNumber : (BitVec.ofNat 64 n).toNat=n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have relation : (index<n)=(index+1≤n) := propext (by omega)
    simp [evalHOLFinite,evalHOLExact,toExact,test,localVar,indexLocal,lengthLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,iNumber,nNumber,
      show index<9223372036854775808 from by omega,show n<9223372036854775808 from by omega,relation]
  · rw [body_shape.2.2.2.2.2.2.2.2.1]
    exact CounterFlow.sequence (ofString "i") _ _ 0 1 (CounterFlow.byte_store (ofString "i") _ _) (CounterFlow.increment_by (ofString "i") 1)

/-- The unchanged activity-bit loop is charged by its actual field count.
Both real callers have fewer than32 fields; failed stores remain covered. -/
theorem bit_loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n index : Nat) (short : n<32) (inside : index≤n)
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    source.clock-(evaluateHOLFiniteState source bitLoop).2.clock≤n-index := by
  rw [body_shape.2.2.2.2.2.2.2.1]
  exact (bit_model source.code n short).cost source.code test bitStep 1 n source index rfl inside position count

theorem bit_loop_globals (key : MlS) (code) : GlobalEffects.Preserves key code bitLoop := by
  rw [body_shape.2.2.2.2.2.2.2.1,body_shape.2.2.2.2.2.2.2.2.1]
  exact GlobalEffects.loop key code _ _ (GlobalEffects.sequence key code _ _ (GlobalEffects.store_byte key code _ _) (GlobalEffects.assign key code _ _))

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.bit_step_summary
#print axioms InitECandidate.Solver.Input.PContainer.bit_step_quiet
#print axioms InitECandidate.Solver.Input.PContainer.bit_model
#print axioms InitECandidate.Solver.Input.PContainer.bit_loop_cost
#print axioms InitECandidate.Solver.Input.PContainer.bit_loop_globals
