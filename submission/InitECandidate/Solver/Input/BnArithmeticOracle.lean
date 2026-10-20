import InitECandidate.Solver.Input.WordArrayCodec

namespace InitECandidate.Solver.Input.BnArithmetic
open Flapjack Flapjack.Basis.Pure.MlString
open RiscvZkvm.Rv64

def modulusOf (words : List Guest.Word) : Nat := Accel.leLimbsToNat ((words.drop 12).take 4)
def output (words : List Guest.Word) : List Guest.Word :=
  words.take 16 ++ Accel.natToLeLimbs 4
    (Accel.arith256Mod (Accel.leLimbsToNat (words.take 4)) (Accel.leLimbsToNat ((words.drop 4).take 4))
      (Accel.leLimbsToNat ((words.drop 8).take 4)) (modulusOf words))

theorem output_length (words : List Guest.Word) (length : words.length = 20) : (output words).length = 20 := by
  simp [output,Accel.natToLeLimbs,length]

/-- The fixed oracle accepts a160byte arithmetic buffer whenever its actual
modulus is nonzero, and preserves the host state. Operand values are arbitrary. -/
theorem oracle (host : Guest.HostMemory) (words : List Guest.Word) (length : words.length = 20) (nonzero : modulusOf words ≠ 0) :
    InitE.sourceOracle (.extCall (ofString "bn_arith256")) host [] (WordArrayCodec.bits words) =
      .ret host (WordArrayCodec.bits (output words)) := by
  have packedLength : (Guest.leBytesOfWords words).length = 160 := by rw [WitnessRadix.Keccak.packed_length,length]
  unfold modulusOf at nonzero
  simp [InitE.sourceOracle,Guest.guestOracle,Guest.acceleratorBytes,Guest.arithModBytes,Guest.exactWords,
    WordArrayCodec.bits,List.map_map,Function.comp_def,bitsToByte_byteToBits,List.map_id',WordArrayCodec.words_roundtrip,
    packedLength,output,modulusOf,nonzero,ofString,toStringOfBytes]

def nextFfi (source : HolFfiState Guest.HostMemory) (words : List Guest.Word) : HolFfiState Guest.HostMemory :=
  {source with ioEvents := source.ioEvents ++
    [{name := .extCall (ofString "bn_arith256"),configuration := [],bytes := (WordArrayCodec.bits words).zip (WordArrayCodec.bits (output words))}]}

theorem call_ffi (source : HolFfiState Guest.HostMemory) (words : List Guest.Word)
    (oracleEq : source.oracle = InitE.sourceOracle) (length : words.length = 20) (nonzero : modulusOf words ≠ 0) :
    callFFIHOL source (.extCall (ofString "bn_arith256")) [] (WordArrayCodec.bits words) =
      .ret (nextFfi source words) (WordArrayCodec.bits (output words)) := by
  have reply : source.oracle (.extCall (ofString "bn_arith256")) source.ffiState [] (WordArrayCodec.bits words) =
      .ret source.ffiState (WordArrayCodec.bits (output words)) := by
    rw [oracleEq]
    exact oracle source.ffiState words length nonzero
  have nonempty : (.extCall (ofString "bn_arith256") : HolFfiName) ≠ .extCall (MlString.implode []) := by decide
  simp [callFFIHOL,nonempty,reply,WordArrayCodec.length,output_length words length,length,nextFfi]

end InitECandidate.Solver.Input.BnArithmetic

#print axioms InitECandidate.Solver.Input.BnArithmetic.output_length
#print axioms InitECandidate.Solver.Input.BnArithmetic.oracle
#print axioms InitECandidate.Solver.Input.BnArithmetic.call_ffi
