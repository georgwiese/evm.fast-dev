import InitECandidate.Solver.WitnessRadix.Keccak256After

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure EntryLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer out : BitVec 64) (length : Nat) : Prop where
  pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))
  outputLocal : source.locals.lookup (ofString "out")=some (.val (.word out))

structure EntryData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (length : Nat) : Prop where
  stateGlobal : source.globals.lookup (ofString "keccak_st")=some (.val (.word stp))
  zeroCode : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)
  hashCode : Code source
  stateAligned : stp.toNat%8=0
  stateFits : stp.toNat+200<2^64
  zeroMapped : ∀ offset,offset+8≤200 → offset%8=0 → source.memaddrs (byteAddress stp offset)
  blockMapped : Mapped source stp pointer length
  tailData : ∀ index,index≤length → length-index<136 → TailData source stp pointer scratch out index (length-index)

theorem EntryData.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (length : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) (data : EntryData source stp pointer scratch out length) :
    EntryData target stp pointer scratch out length := by
  have globals : target.globals=source.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
    exact h
  have codes : target.code=source.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control
    exact h
  have domain : target.memaddrs=source.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
    exact h
  constructor
  · simpa only [globals] using data.stateGlobal
  · simpa only [codes] using data.zeroCode
  · exact Code.of_control source target control data.hashCode
  · exact data.stateAligned
  · exact data.stateFits
  · simpa only [domain] using data.zeroMapped
  · exact mapped_of_control source target _ _ _ control data.blockMapped
  · intro index ordered small
    exact TailData.of_control source target _ _ _ _ _ _ control (data.tailData index ordered small)

def Protected (stp scratch out query : BitVec 64) : Prop :=
  CopyGeneral.Away stp query 200 ∧ CopyGeneral.Away scratch query 136 ∧ CopyGeneral.Away out query 32

theorem Protected.tail (stp scratch out query : BitVec 64) (protection : Protected stp scratch out query) : Away stp scratch out query := by
  refine ⟨⟨?_,?_⟩,protection.2⟩
  · intro word
    exact (protection.1 (8*word.val) (by have := word.isLt; omega)).1
  · intro offset inside
    exact (protection.1 offset inside).2

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.EntryData.of_control
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Protected.tail
