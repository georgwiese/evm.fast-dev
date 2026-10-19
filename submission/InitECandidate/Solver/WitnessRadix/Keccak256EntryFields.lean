import InitECandidate.Solver.WitnessRadix.Keccak256Entry

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The hash's mapping/environment obligations use two scratch globals,
the code map, memory domain and oracle. In particular, changing the heap
cursor and lexical locals does not require new future hash facts. -/
theorem EntryData.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (domain : target.memaddrs=source.memaddrs) (codes : target.code=source.code)
    (oracle : target.ffi.oracle=source.ffi.oracle)
    (state : target.globals.lookup (ofString "keccak_st")=source.globals.lookup (ofString "keccak_st"))
    (pad : target.globals.lookup (ofString "keccak_pad")=source.globals.lookup (ofString "keccak_pad"))
    (data : EntryData source stp pointer scratch out length) : EntryData target stp pointer scratch out length := by
  have hashCode : Code target := ⟨by rw [codes]; exact data.hashCode.block,
    by rw [codes]; exact data.hashCode.perm,oracle.trans data.hashCode.oracleEq⟩
  constructor
  · exact state.trans data.stateGlobal
  · rw [codes]; exact data.zeroCode
  · exact hashCode
  · exact data.stateAligned
  · exact data.stateFits
  · simpa only [domain] using data.zeroMapped
  · intro index inside
    exact KeccakAbsorb.Mapped.of_domain source target _ _ _ domain (data.blockMapped index inside)
  · intro index ordered small
    let old := data.tailData index ordered small
    exact {
      zeroCode := by rw [codes]; exact old.zeroCode
      copyCode := by rw [codes]; exact old.copyCode
      hashCode := hashCode
      scratchGlobal := pad.trans old.scratchGlobal
      scratchAligned := old.scratchAligned
      stateAligned := old.stateAligned
      stateFits := old.stateFits
      zeroMapped := by simpa only [domain] using old.zeroMapped
      copyMapped := CopyContext.Mapped.of_domain source target _ _ _ domain old.copyMapped
      absorbMapped := KeccakAbsorb.Mapped.of_domain source target _ _ _ domain old.absorbMapped
      outputMapped := OutMapped.of_domain source target _ _ domain old.outputMapped
      firstMapped := by simpa only [domain] using old.firstMapped
      lastMapped := by simpa only [domain] using old.lastMapped }

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.EntryData.of_fields
