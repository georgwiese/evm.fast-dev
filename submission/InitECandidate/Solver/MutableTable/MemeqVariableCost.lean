import InitECandidate.Solver.MutableTable.MemeqAnyCost
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.Input.MemeqCode
import InitECandidate.Solver.Input.ClockCostCallReached

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

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A successful original comparison ABI supplies its actual constant
length even when either operand expression might otherwise fail. -/
theorem fixed_argument_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64) (length : Nat)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,.const (BitVec.ofNat 64 length)]=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "memeq") values=some (actual,callee,shape)) :
    actual=Memeq32.body ∧ callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := by
  cases firstRead : eval source first with
  | none=>
    simp only [eval] at firstRead
    simp [evalListHOLFinite,evalListHOLExact,firstRead] at args
  | some left=>
    cases secondRead : eval source second with
    | none=>
      simp only [eval] at firstRead secondRead
      simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead] at args
    | some right=>
      let actualValues : List (ValueHOL 64):=[left,right,.val (.word (BitVec.ofNat 64 length))]
      have expected : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,.const (BitVec.ofNat 64 length)]=some actualValues:=by
        simp only [eval] at firstRead secondRead
        simp [actualValues,evalListHOLFinite,evalListHOLExact,firstRead,secondRead,evalHOLExact]
      have valuesEq:=Option.some.inj (args.symm.trans expected)
      rw [valuesEq] at called
      cases left <;> cases right
      case val.val a b=>
        cases a with
        | word a=>
          cases b with
          | word b=>
            obtain ⟨known,lookup,aCell,bCell,nCell⟩:=MemeqByteRuntime.environment source.code.lookup a b length code
            have same:=Option.some.inj (called.symm.trans lookup)
            have bodyEq : actual=Memeq32.body:=congrArg Prod.fst same
            have calleeEq : callee=known:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
            rw [←calleeEq] at nCell
            exact ⟨bodyEq,nCell⟩
      all_goals
        have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") actualValues=none:=by
          apply (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr
          unfold lookupCodeHOLExact
          rw [code]
          simp [actualValues,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
        rw [failed] at called
        cases called

/-- Original ignored/local/tail comparison calls at any fixed length up
to 64, including malformed or unmapped operand reads and exhausted clocks. -/
theorem fixed_call_cost (code) (installed : Input.OriginalCode.Installed code) (destination : Option (Option MlS))
    (first second : ExpHOL 64) (length : Nat) (small : length≤64) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination) (ofString "memeq") [first,second,.const (BitVec.ofNat 64 length)]) (4*length+1) := by
  intro source sameCode
  apply Input.ClockCost.call_arguments_current source destination (ofString "memeq") _ (4*length)
  intro values actual callee shape args called
  obtain ⟨bodyEq,nCell⟩:=fixed_argument_entry source first second length
    (original_code source.code (sameCode.symm ▸ installed)) values actual callee shape args called
  rw [bodyEq]
  exact variable_body_cost (callEntryStateHOLFinite source callee) length small nCell

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.fixed_argument_entry
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.fixed_call_cost
