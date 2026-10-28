import InitECandidate.Solver.Input.PackBytesProgram
import InitECandidate.Solver.WitnessRadix.ZeroEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesArguments
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem amount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : Nat)
    (count : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 (PackBytes.chunks n))))) :
    eval source PackBytes.amountExpression = some (.val (.word (BitVec.ofNat 64 (PackBytes.padded n)))) := by
  simp [eval,PackBytes.amountExpression,localVar,evalHOLExact,evalListHOLExact,toExact,count,
    valueIsWord,valueWord,panOpHOL,PackBytes.padded,BitVec.ofNat_mul,BitVec.mul_comm]

/-- The actual packer's padding call uses exactly its returned chunk count,
with at most31bytes; word subtraction is justified by the real length bound. -/
theorem zero_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64) (n : Nat)
    (small : n+64<2^64)
    (buf : source.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (length : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (count : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 (PackBytes.chunks n))))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) PackBytes.zeroArguments =
      some (Zero.values (buffer+BitVec.ofNat 64 n) (PackBytes.padded n-n)) := by
  have bounds := PackBytes.padding_bounds n
  have difference := BitVec.ofNat_sub_ofNat_of_le (w := 64) (PackBytes.padded n) n (by omega) bounds.1
  have amount : BitVec.ofNat 64 (PackBytes.chunks n) * 32#64 = BitVec.ofNat 64 (PackBytes.padded n) := by
    change BitVec.ofNat 64 (PackBytes.chunks n) * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul]
    congr 1
    unfold PackBytes.padded
    omega
  have padding : BitVec.ofNat 64 (PackBytes.chunks n) * 32#64 - BitVec.ofNat 64 n = BitVec.ofNat 64 (PackBytes.padded n - n) := by
    rw [amount, difference]
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, PackBytes.zeroArguments, PackBytes.amountExpression, localVar,
    buf, length, count, Zero.values, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, padding]

end InitECandidate.Solver.Input.CurrentHash.PackBytesArguments

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesArguments.amount_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesArguments.zero_arguments
