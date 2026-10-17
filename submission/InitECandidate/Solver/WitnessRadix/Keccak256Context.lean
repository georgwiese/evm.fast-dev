import InitECandidate.Solver.WitnessRadix.Keccak256Block

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack PanSemStateFiniteExact

theorem Mapped.of_domain {F : Type} (source target : PanSemStateFiniteExact 64 F) (stp blk : BitVec 64) (unaligned : Bool)
    (domain : target.memaddrs=source.memaddrs) (mapped : Mapped source stp blk unaligned) : Mapped target stp blk unaligned := by
  constructor
  · simpa only [domain] using mapped.stateWords
  · simpa only [domain] using mapped.blockWords
  · simpa only [domain] using mapped.blockBytes

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem Code.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) (code : Code source) : Code target := by
  constructor
  · have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code.lookup (ofString "keccak_absorb_block")) control
    exact h.trans code.block
  · have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code.lookup (ofString "keccak_f1600")) control
    exact h.trans code.perm
  · have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.oracle) control
    exact h.trans code.oracleEq

theorem mapped_of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (length : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) (mapped : Mapped source stp pointer length) :
    Mapped target stp pointer length := by
  have domain : target.memaddrs=source.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
    exact h
  intro index inside
  exact KeccakAbsorb.Mapped.of_domain source target _ _ _ domain (mapped index inside)

theorem Args.of_index (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (length : Nat) (index : BitVec 64)
    (locals : target.locals=(bind source "i" index).locals) (args : Args source stp pointer length) : Args target stp pointer length := by
  constructor
  · rw [locals,bind_lookup_other source "i" "stp" index (by decide)]; exact args.stateLocal
  · rw [locals,bind_lookup_other source "i" "p" index (by decide)]; exact args.pointerLocal
  · rw [locals,bind_lookup_other source "i" "n" index (by decide)]; exact args.lengthLocal

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index length : Nat)
    (small : length+136<2^64) (ordered : index≤length)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition =
      some (.val (.word (if index+136≤length then 1#64 else 0#64))) := by
  have lengthSmall : length<2^64 := by omega
  have sum : (BitVec.ofNat 64 index + 136#64).toNat=index+136 := by
    rw [BitVec.toNat_add_of_lt]
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      rfl
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      change index+136<2^64
      omega
  have lower : (BitVec.ofNat 64 length < BitVec.ofNat 64 index + 136#64) ↔ length < index+136 := by
    change (BitVec.ofNat 64 length).toNat < _ ↔ _
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthSmall,sum]
  by_cases active : index+136≤length
  all_goals simp [condition,localVar,addConst,evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,indexLocal,lengthLocal,
    valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,lower,active]

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.Mapped.of_domain
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Code.of_control
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.mapped_of_control
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Args.of_index
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.condition_read
