import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString AllocatedBytes

structure Buffers (stp pointer scratch out : BitVec 64) (length : Nat) : Prop where
  stateArena : Arena stp 200
  stateAligned : stp.toNat%8=0
  inputArena : Arena pointer length
  scratchArena : Arena scratch 136
  scratchAligned : scratch.toNat%8=0
  outputArena : Arena out 32

structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp scratch : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  stateGlobal : source.globals.lookup (ofString "keccak_st")=some (.val (.word stp))
  scratchGlobal : source.globals.lookup (ofString "keccak_pad")=some (.val (.word scratch))
  zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)
  copyCode : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one)
  hashCode : Code source

theorem absorb_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (stateArena : Arena stp 200) (blockArena : Arena blk 136) (aligned : stp.toNat%8=0) :
    KeccakAbsorb.Mapped source stp blk (KeccakAbsorb.isUnaligned blk) := by
  constructor
  · intro word
    exact word_mapped source stp 200 (8*word.val) domain stateArena (by have := word.isLt; omega) aligned (by omega)
  · intro unaligned lane
    have mask : blk &&& 7#64=0#64 := by simpa [KeccakAbsorb.isUnaligned] using unaligned
    exact word_mapped source blk 136 (8*lane.val) domain blockArena (by have := lane.isLt; omega) (mask_aligned blk mask) (by omega)
  · intro offset
    exact byte_mapped source blk 136 offset.val domain blockArena offset.isLt

theorem out_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (stateArena : Arena stp 200) (outputArena : Arena out 32) (aligned : stp.toNat%8=0) :
    OutMapped source stp out := by
  constructor
  · exact copy_mapped source stp out 32 domain (Arena.weaken stp 200 32 stateArena (by decide)) outputArena
  · intro offset inside offsetAligned
    exact word_mapped source stp 200 offset domain stateArena (by omega) aligned offsetAligned
  · intro mask offset inside offsetAligned
    exact word_mapped source out 32 offset domain outputArena inside (mask_aligned out mask) offsetAligned

/-- All hash read/write mapping premises follow from six natural arena/align
facts and the actual source domain, rather than per-cell execution assumptions. -/
theorem allocated_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (length : Nat)
    (environment : Environment source stp scratch) (buffers : Buffers stp pointer scratch out length) :
    EntryData source stp pointer scratch out length := by
  have stateFits : stp.toNat+200<2^64 := by have := buffers.stateArena.upper; omega
  constructor
  · exact environment.stateGlobal
  · exact environment.zeroCode
  · exact environment.hashCode
  · exact buffers.stateAligned
  · exact stateFits
  · intro offset inside aligned
    exact word_mapped source stp 200 offset environment.domain buffers.stateArena (by omega) buffers.stateAligned aligned
  · intro index inside
    exact absorb_mapped source stp (byteAddress pointer index) environment.domain buffers.stateArena
      (Arena.subrange pointer length index 136 buffers.inputArena inside) buffers.stateAligned
  · intro index ordered remBound
    constructor
    · exact environment.zeroCode
    · exact environment.copyCode
    · exact environment.hashCode
    · exact environment.scratchGlobal
    · exact buffers.scratchAligned
    · exact buffers.stateAligned
    · exact stateFits
    · intro offset inside aligned
      exact word_mapped source scratch 136 offset environment.domain buffers.scratchArena (by omega) buffers.scratchAligned aligned
    · exact copy_mapped source (byteAddress pointer index) scratch (length-index) environment.domain
        (Arena.subrange pointer length index (length-index) buffers.inputArena (by omega))
        (Arena.weaken scratch 136 (length-index) buffers.scratchArena (by omega))
    · exact absorb_mapped source stp scratch environment.domain buffers.stateArena buffers.scratchArena buffers.stateAligned
    · exact out_mapped source stp out environment.domain buffers.stateArena buffers.outputArena buffers.stateAligned
    · exact byte_mapped source scratch 136 (length-index) environment.domain buffers.scratchArena remBound
    · exact byte_mapped source scratch 136 135 environment.domain buffers.scratchArena (by decide)

theorem allocated_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (code : source.code.lookup (ofString "keccak256")=some (formals,body,.one))
    (environment : Environment source stp scratch) (buffers : Buffers stp pointer scratch out length) (enough : price length+1≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,output) ∧
      output.locals=source.locals ∧ output.clock≤source.clock ∧ source.clock-(price length+1)≤output.clock ∧
      KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,Protected stp scratch out query → output.memory query=source.memory query := by
  have small : length+136<2^64 := by have := buffers.inputArena.upper; omega
  exact call_execute source arguments stp pointer scratch out length args code (allocated_entry source stp pointer scratch out length environment buffers) small enough

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.absorb_mapped
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.out_mapped
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.allocated_entry
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.allocated_call
