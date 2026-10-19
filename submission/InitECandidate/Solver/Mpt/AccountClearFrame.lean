import InitECandidate.Solver.Mpt.AccountDecodeOutput
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual fixed32-byte balance clear preserves every ordinary word
outside the account. Its successful execution/funding is derived by the
normal clear contract, without a memory-clearing oracle. -/
theorem clear_window (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (cell : source.locals.lookup (ofString "acct_out")=some (.val (.word out))) (output : Output out)
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source clearCall=(none,post)) : Rlp.Slices.Window source post out.toNat (out.toNat+56) := by
  obtain ⟨positive,same⟩ := clear_none source post out cell output domain installed normal
  intro query outside
  rw [same]
  change Zero.finalMemory source.memory (out+8#64) 32 query=source.memory query
  apply Zero.final_memory_away
  intro offset inside
  have number : (byteAddress (out+8#64) offset).toNat=out.toNat+8+offset := by
    rw [byteAddress_toNat _ _ (by rw [output.clear_number out]; have := output.upper; omega),output.clear_number out]
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [number] at numeric
  rcases outside with before|after <;> omega

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.clear_window
