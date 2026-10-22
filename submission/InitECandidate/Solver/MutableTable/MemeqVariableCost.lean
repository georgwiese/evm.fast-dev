import InitECandidate.Solver.MutableTable.MemeqAnyCost

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem variable_block_test_reads (stride length : Nat) (strideBound : stride≤32) (small : length≤64) :
    Input.GuardedCounterLoop.TestReads (blockTest stride) stride length := by
  intro source word cell nCell bounded
  have strideSmall : stride<2^64:=by omega
  have lengthMod : length%18446744073709551616=length:=Nat.mod_eq_of_lt (by omega)
  have number : (word+BitVec.ofNat 64 stride).toNat=word.toNat+stride:=by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt strideSmall]
  have compare : ((BitVec.ofNat 64 length : BitVec 64)<word+BitVec.ofNat 64 stride)↔length<word.toNat+stride:=by
    simp only [BitVec.lt_def,number,BitVec.toNat_ofNat,lengthMod]
  by_cases active : word.toNat+stride≤length
  · have below : ¬length<word.toNat+stride:=by omega
    simp [blockTest,evalHOLFinite,evalHOLExact,evalListHOLExact,localVar,toExact,cell,nCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,below]
  · have above : length<word.toNat+stride:=by omega
    simp [blockTest,evalHOLFinite,evalHOLExact,evalListHOLExact,localVar,toExact,cell,nCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,above]

theorem variable_byte_test_reads (length : Nat) (small : length≤64) :
    Input.GuardedCounterLoop.TestReads Memeq32.condition1 1 length := by
  intro source word cell nCell bounded
  have lengthMod : length%18446744073709551616=length:=Nat.mod_eq_of_lt (by omega)
  have compare : ((word : BitVec 64)<BitVec.ofNat 64 length)↔word.toNat<length:=by
    simp only [BitVec.lt_def,BitVec.toNat_ofNat,lengthMod]
  by_cases active : word.toNat+1≤length
  · have below : word.toNat<length:=by omega
    simp [Memeq32.condition1,evalHOLFinite,evalHOLExact,localVar,toExact,cell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,below]
  · have above : ¬word.toNat<length:=by omega
    simp [Memeq32.condition1,evalHOLFinite,evalHOLExact,localVar,toExact,cell,nCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,compare,active,above]

/-- The original comparison for every actual length up to64, including
unmapped or malformed operand reads. Four literal loops give a uniform
fallback; mapped comparisons retain their sharper existing bound. -/
theorem variable_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length≤64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source Memeq32.body).2.clock≤4*length := by
  have other : Model Memeq32.parts.otherAligned (length+length) length:=by
    rw [other_shape]
    simpa only [Nat.zero_add] using (Model.decision decisions.2.2).sequence
      ((Model.loop (blockTest 32) word32Body 32 (by decide) guarded_bodies.1 (variable_block_test_reads 32 length (by decide) small) small).sequence
        (Model.loop (blockTest 8) word8Body 8 (by decide) guarded_bodies.2.1 (variable_block_test_reads 8 length (by decide) small) small))
  have tail : Model Memeq32.parts.tailCode (length+length) length:=by
    rw [Memeq32.tail_shape]
    exact (Model.loop Memeq32.condition8 Memeq32.byteBodies.1 8 (by decide) guarded_bodies.2.2.1 (variable_block_test_reads 8 length (by decide) small) small).sequence
      ((Model.loop Memeq32.condition1 Memeq32.byteBodies.2 1 (by decide) guarded_bodies.2.2.2 (variable_byte_test_reads length small) small).sequence
        (Model.decision (.returned (.const 1#64))))
  have skipModel : Model .skip 0 length:=Model.decision .skip
  have twenty:=Model.conditional (Memeq32.sizeTest 20#64) (Model.decision decisions.1) skipModel
  have thirtyTwo:=Model.conditional (Memeq32.sizeTest 32#64) (Model.decision decisions.2.1) skipModel
  have phase:=Model.conditional Memeq32.alignmentTest (twenty.sequence (thirtyTwo.sequence other)) skipModel
  have inside:=phase.sequence tail
  rw [Memeq32.body_shape]
  apply Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 _ (4*length) rfl
  let entered:=bind source "i" 0#64
  have valid : Input.GuardedCounterLoop.Invariant length entered:=⟨0#64,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by change 0≤length; omega⟩
  have price:=inside.cost entered valid
  simp only [Nat.zero_add,Nat.add_zero,Nat.max_zero,Nat.zero_max] at price
  change entered.clock-(evaluateHOLFiniteState entered _).2.clock≤4*length
  omega

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.variable_block_test_reads
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.variable_byte_test_reads
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.variable_body_cost
