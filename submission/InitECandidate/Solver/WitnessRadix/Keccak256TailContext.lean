import InitECandidate.Solver.WitnessRadix.Keccak256Output
import InitECandidate.Solver.WitnessRadix.Keccak256PadStores

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure TailLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer out : BitVec 64) (index rem : Nat) : Prop where
  stateLocal : source.locals.lookup (ofString "stp")=some (.val (.word stp))
  pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  outputLocal : source.locals.lookup (ofString "out")=some (.val (.word out))
  indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  remLocal : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))

structure TailData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (index rem : Nat) : Prop where
  zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)
  copyCode : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one)
  hashCode : Code source
  scratchGlobal : source.globals.lookup (ofString "keccak_pad")=some (.val (.word scratch))
  scratchAligned : scratch.toNat%8=0
  stateAligned : stp.toNat%8=0
  stateFits : stp.toNat+200<2^64
  zeroMapped : ∀ offset,offset+8≤136 → offset%8=0 → source.memaddrs (byteAddress scratch offset)
  copyMapped : CopyContext.Mapped source (byteAddress pointer index) scratch rem
  absorbMapped : KeccakAbsorb.Mapped source stp scratch (KeccakAbsorb.isUnaligned scratch)
  outputMapped : OutMapped source stp out
  firstMapped : source.memaddrs (panByteAlignHOL (width := 64) (byteAddress scratch rem))
  lastMapped : source.memaddrs (panByteAlignHOL (width := 64) (scratch+135#64))

theorem TailLocals.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer out : BitVec 64) (index rem : Nat)
    (same : target.locals=source.locals) (locals : TailLocals source stp pointer out index rem) : TailLocals target stp pointer out index rem := by
  constructor
  · simpa only [same] using locals.stateLocal
  · simpa only [same] using locals.pointerLocal
  · simpa only [same] using locals.outputLocal
  · simpa only [same] using locals.indexLocal
  · simpa only [same] using locals.remLocal

theorem OutMapped.of_domain (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64)
    (domain : target.memaddrs=source.memaddrs) (mapped : OutMapped source stp out) : OutMapped target stp out := by
  constructor
  · exact CopyContext.Mapped.of_domain source target stp out 32 domain mapped.copy
  · simpa only [domain] using mapped.stateWords
  · simpa only [domain] using mapped.outputWords

theorem TailData.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (index rem : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) (data : TailData source stp pointer scratch out index rem) :
    TailData target stp pointer scratch out index rem := by
  have codes : target.code=source.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control
    exact h
  have globals : target.globals=source.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
    exact h
  have domain : target.memaddrs=source.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
    exact h
  constructor
  · simpa only [codes] using data.zeroCode
  · simpa only [codes] using data.copyCode
  · exact Code.of_control source target control data.hashCode
  · simpa only [globals] using data.scratchGlobal
  · exact data.scratchAligned
  · exact data.stateAligned
  · exact data.stateFits
  · simpa only [domain] using data.zeroMapped
  · exact CopyContext.Mapped.of_domain source target _ _ _ domain data.copyMapped
  · exact KeccakAbsorb.Mapped.of_domain source target _ _ _ domain data.absorbMapped
  · exact OutMapped.of_domain source target _ _ domain data.outputMapped
  · simpa only [domain] using data.firstMapped
  · simpa only [domain] using data.lastMapped

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.TailLocals.of_locals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.OutMapped.of_domain
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.TailData.of_control
