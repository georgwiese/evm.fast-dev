import InitECandidate.Solver.Headers.CurrentValidate.DecodeStep
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original signed loop test is a natural comparison on the actual
small reached counter/count words, including the zero-header link test. -/
theorem test_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count+1) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if index<data.count then 1#64 else 0#64))) := by
  have countSmall : data.count<9223372036854775808 := by have h:=layout.count; omega
  have indexSmall : index<9223372036854775808 := by have h:=layout.count; omega
  have countNumber : (BitVec.ofNat 64 data.count).toNat=data.count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have indexNumber : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [test,evalHOLFinite,evalHOLExact,localVar,toExact,state.indexCell,state.countCell,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,countNumber,indexNumber,countSmall,indexSmall]

theorem active_of_test (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count+1) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word word)))
    (nonzero : word≠0#64) : index<data.count := by
  have actual:=test_read data origin source index state layout bounded
  apply Classical.byContradiction
  intro inactive
  rw [if_neg inactive] at actual
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans actual
  exact nonzero zero

theorem decode_step_local : Input.LocalPrefix (ofString "n") decodeStep := by
  obtain ⟨_,_,_,_,_,_,_,decodeShape,headerShape,_,_⟩ := shapes
  rw [decodeShape,headerShape]
  exact .decCall (ofString "h") .one (ofString "decode_header") decodeArguments (by decide)
    (.seq (.store _ _) (.seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide))))

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.test_read
#print axioms InitECandidate.Solver.Headers.CurrentValidate.active_of_test
#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_step_local
