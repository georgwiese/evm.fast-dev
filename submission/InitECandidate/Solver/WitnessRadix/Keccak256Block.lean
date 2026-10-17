import InitECandidate.Solver.WitnessRadix.Keccak256Program

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

structure Args (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (length : Nat) : Prop where
  stateLocal : source.locals.lookup (ofString "stp") = some (.val (.word stp))
  pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer))
  lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))

structure Code (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  block : source.code.lookup (ofString "keccak_absorb_block") = some (KeccakAbsorb.formals,KeccakAbsorb.body,.one)
  perm : source.code.lookup (ofString "keccak_f1600") = some (Keccak.formals,Keccak.f1600Body,.one)
  oracleEq : source.ffi.oracle = InitE.sourceOracle

def Mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (length : Nat) : Prop :=
  ∀ index, index+136 ≤ length → KeccakAbsorb.Mapped source stp (byteAddress pointer index) (KeccakAbsorb.isUnaligned (byteAddress pointer index))

theorem block_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer : BitVec 64) (index length : Nat)
    (args : Args source stp pointer length) (code : Code source) (mapped : Mapped source stp pointer length)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index+136 ≤ length) (aligned : stp.toNat%8=0) (fits : stp.toNat+200<2^64) (enough : 19 ≤ source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source blockBody = (none,output) ∧
      output.clock=source.clock-19 ∧ KeccakAbsorb.hashControl output = KeccakAbsorb.hashControl source ∧
      output.locals = (bind source "i" (BitVec.ofNat 64 (index+136))).locals ∧
      ∀ query : BitVec 64, KeccakAbsorb.Away stp query → output.memory query = source.memory query := by
  classical
  have evaluated : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) blockArguments =
      some (KeccakAbsorb.values stp (byteAddress pointer index)) := by
    simp [blockArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,args.stateLocal,args.pointerLocal,indexLocal,
      valueIsWord,valueWord,wordOpHOL,wordOp,KeccakAbsorb.values,byteAddress]
  obtain ⟨called,run,locals,clock,control,memory⟩ := KeccakAbsorb.call_execute source blockArguments stp (byteAddress pointer index)
    evaluated code.block code.perm code.oracleEq aligned fits (mapped index inside) enough
  have index' : called.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := by rw [locals]; exact indexLocal
  have incremented := StateSteps.assign_execute called "i" (addConst (localVar "i") 136#64) (BitVec.ofNat 64 index)
    (BitVec.ofNat 64 (index+136)) index' (by
      simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,index',valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add])
  refine ⟨bind called "i" (BitVec.ofNat 64 (index+136)),?_,clock,control,?_,memory⟩
  · rw [blockBody,StateSteps.next_sequence source called _ _ run (by omega)]
    exact incremented
  · simp only [QueryBranch.bind,setVarHOLFinite,locals]

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.block_execute
