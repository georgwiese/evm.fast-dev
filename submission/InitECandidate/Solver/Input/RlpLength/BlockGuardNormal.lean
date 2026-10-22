import InitECandidate.Solver.Input.RlpLength.BlockGuard
import InitECandidate.Solver.Input.NoReturnScoped

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem guard_pass (source : PanSemStateFiniteExact 64 Guest.HostMemory) (encoded : Nat)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded) (small : encoded≤8388608) :
    evaluateHOLFiniteState source sizeGuard=(none,source) := by
  have comparison : ¬8388608#64<BitVec.ofNat 64 encoded:=by
    change ¬(8388608#64).toNat<(BitVec.ofNat 64 encoded).toNat
    rw [number]
    change ¬8388608<encoded
    omega
  have testRead : eval source sizeTest=some (.val (.word 0#64)):=by
    simp [eval,sizeTest,localVar,evalHOLExact,toExact,bl,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison]
  simp only [eval] at testRead
  rw [sizeGuard,evaluateHOLFiniteState_ite,testRead]
  simp

/-- A real normal continuation passed the original computed-size guard.
Even an absent/wrong exception shape cannot let its raise return normally. -/
theorem guarded_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (encoded : Nat)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (bl : source.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (number : (BitVec.ofNat 64 encoded).toNat=encoded)
    (normal : evaluateHOLFiniteState source (.seq sizeGuard continuation)=(some (.returned value),post)) :
    encoded≤8388608 := by
  by_contra big
  have comparison : 8388608#64<BitVec.ofNat 64 encoded:=by
    change (8388608#64).toNat<(BitVec.ofNat 64 encoded).toNat
    rw [number]
    change 8388608<encoded
    omega
  have testRead : eval source sizeTest=some (.val (.word 1#64)):=by
    simp [eval,sizeTest,localVar,evalHOLExact,toExact,bl,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison]
  have guardEq : evaluateHOLFiniteState source sizeGuard=evaluateHOLFiniteState source (.raise (ofString "BlockErr") (.const 7#64)):=by
    simp only [eval] at testRead
    rw [sizeGuard,evaluateHOLFiniteState_ite,testRead]
    rfl
  have same : evaluateHOLFiniteState source (.seq sizeGuard continuation)=
      evaluateHOLFiniteState source (.seq (.raise (ofString "BlockErr") (.const 7#64)) continuation):=by
    simp only [evaluateHOLFiniteState_seq_line780,guardEq]
  rw [same] at normal
  exact NoReturn.raised_sequence (ofString "BlockErr") (.const 7#64) continuation source value (congrArg Prod.fst normal)

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.guarded_normal
#print axioms InitECandidate.Solver.Input.RlpLength.Block.guard_pass
