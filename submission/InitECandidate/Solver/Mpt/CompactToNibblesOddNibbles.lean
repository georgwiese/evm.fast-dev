import InitECandidate.Solver.Mpt.CompactToNibblesOdd
import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedCall

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The genuine optional compact-path store establishes its actual first
nibble. The zero alternative has an empty prefix. Source c0 is the real
loaded byte; later conversion will preserve this prefix byte by byte. -/
theorem odd_nibbles (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (out odd : BitVec 64) (byte : BitVec 8)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (byteCell : source.locals.lookup (ofString "c0")=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word 0#64)))
    (little : source.be=false) (mapped : source.memaddrs (panByteAlignHOL (width:=64) out))
    (normal : evaluateHOLFiniteState source oddGuard=(none,target)) :
    ∃ k : BitVec 64,(k=0#64 ∨ k=1#64) ∧ target.locals.lookup (ofString "k")=some (.val (.word k)) ∧
      KeyToNibbles.NibblePrefix target out k.toNat := by
  by_cases zero : odd=0#64
  · have skipped : evaluateHOLFiniteState source oddGuard=(none,source):=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have same : target=source:=congrArg Prod.snd (normal.symm.trans skipped)
    rw [same]
    refine ⟨0#64,Or.inl rfl,kCell,?_⟩
    intro position impossible
    change position<0 at impossible
    omega
  · have address : eval source (localVar "out")=some (.val (.word out)):=by simp [eval,localVar,evalHOLExact,toExact,outCell]
    have value:=KeyToNibbles.low_read source "c0" byte byteCell
    let stored:={source with memory:=ByteStore.put source.memory source.be out (KeyToNibbles.low byte)}
    have storeRun : evaluateHOLFiniteState source (.storeByte (localVar "out") (.op .and [localVar "c0",.const 15#64]))=(none,stored):=
      ByteStore.execute source _ _ out (KeyToNibbles.low byte) address value mapped
    have assigned:=StateSteps.assign_execute stored "k" (.const 1#64) 0#64 1#64 kCell rfl
    have write : evaluateHOLFiniteState source oddWrite=(none,bind stored "k" 1#64):=by
      rw [oddWrite,evaluateHOLFiniteState_seq_line780,storeRun]
      exact assigned
    have taken : evaluateHOLFiniteState source oddGuard=evaluateHOLFiniteState source oddWrite:=by
      simp [oddGuard,oddTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,oddCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have same : target=bind stored "k" 1#64:=congrArg Prod.snd (normal.symm.trans (taken.trans write))
    rw [same]
    refine ⟨1#64,Or.inr rfl,bind_lookup_same _ _ _,?_⟩
    intro position inside
    have positionZero : position=0:=by change position<1 at inside; omega
    subst position
    refine ⟨UInt8.ofNat (KeyToNibbles.low byte).toNat,?_,?_⟩
    · rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt (by have bound:=KeyToNibbles.low_small byte; omega)]
      exact KeyToNibbles.low_small byte
    · change @panMemLoadByteHOL 64 _ (ByteStore.put source.memory source.be out (KeyToNibbles.low byte)) source.memaddrs
        (fun query=>Classical.propDecidable (source.memaddrs query)) source.be (byteAddress out 0)=_
      simp only [byteAddress,BitVec.add_zero]
      rw [little]
      exact ByteStore.read_self source.memory source.memaddrs out (KeyToNibbles.low byte) mapped

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.odd_nibbles
