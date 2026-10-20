import InitECandidate.Solver.Input.ZeroShortLoops
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.ZeroShort
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem unaligned_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat)
    (short : length<32) (unaligned : dst.toNat%8≠0)
    (pointer : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source Zero.body).2.clock≤62 := by
  let entry := bind source "i" 0#64
  have entryN : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthLocal
  have entryDst : entry.locals.lookup (ofString "dst")=some (.val (.word dst)) := (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans pointer
  have mask : dst &&& 7#64≠0#64 := by
    intro zero
    have number:=congrArg BitVec.toNat zero
    rw [BitVec.toNat_and] at number
    change dst.toNat &&& 7=0 at number
    rw [show 7=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod] at number
    exact unaligned number
  have read : eval entry Zero.alignment=some (.val (.word 0#64)) := by
    simp [eval,Zero.alignment,localVar,evalHOLExact,evalListHOLExact,toExact,entryDst,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,mask]
  have skipped : evaluateHOLFiniteState entry (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip)=(none,entry) := by
    simp only [eval] at read
    rw [evaluateHOLFiniteState_ite,read]
    exact evaluateHOLFiniteState_skip entry
  rw [Zero.body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 62 rfl
  rw [StateSteps.next_sequence entry entry _ _ skipped (Nat.le_refl _)]
  have byteModel := byte_model source.code length short
  have firstCost := Model.cost source.code (Zero.condition 8#64) Zero.byteBody 8 length byteModel entry 0 rfl (Nat.zero_le _) (bind_lookup_same _ _ _) entryN
  rw [←Zero.other_loop_shapes.1] at firstCost
  have front : entry.clock-(evaluateHOLFiniteState entry Zero.loopBytes).2.clock≤length := by simpa only [Nat.sub_zero] using firstCost
  have price := ClockCost.sequence_reached_current entry Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64))) length length front (by
    intro middle normal
    have nextValid := Model.normal source.code (Zero.condition 8#64) Zero.byteBody 8 length byteModel entry middle rfl ⟨0,Nat.zero_le _,bind_lookup_same _ _ _,entryN⟩
      (by rw [←Zero.other_loop_shapes.1]; exact normal)
    obtain ⟨index,inside,currentI,currentN⟩ := nextValid
    have fields := evaluation_fields entry middle Zero.loopBytes none normal
    have tailCost := Model.cost source.code (.cmp .lower (localVar "i") (localVar "n")) Zero.tailBody 1 length (tail_model source.code length short)
      middle index fields.2.2.2 inside currentI currentN
    rw [←Zero.other_loop_shapes.2] at tailCost
    exact ClockCost.sequence_current middle Zero.loopTail (.return (.const 0#64)) length 0 (by omega) (ClockCost.returned middle.code _))
  change entry.clock-(evaluateHOLFiniteState entry (.seq Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64))))).2.clock≤62
  omega

/-- Original short unaligned zero calls need no successful-store premise.
Every loop outcome spends at most63 source clocks including its caller. -/
theorem unaligned_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (short : length<32) (unaligned : dst.toNat%8≠0)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (code : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)).2.clock≤63 := by
  obtain ⟨callee,called,dstLocal,lengthLocal⟩ := Zero.environment source.code.lookup dst length code
  have bodyCost := unaligned_body_cost (callEntryStateHOLFinite source callee) dst length short unaligned dstLocal lengthLocal
  exact ClockCost.call_current source (some none) (ofString "memzero") arguments (Zero.values dst length) Zero.body callee .one 62 args called bodyCost

/-- Actual pack_bytes padding satisfies the aligned-multiple alternative;
its unaligned alternative follows the original byte8/byte1 loops. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (short : length<32) (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena dst length) (alignedMultiple : dst.toNat%8=0 → length%8=0) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)).2.clock≤63 := by
  by_cases aligned : dst.toNat%8=0
  · have price := Zero.call_cost source arguments dst length args (Zero.original_code source.code installed) (by omega) (alignedMultiple aligned) aligned
      (by intro index inside multiple; exact AllocatedBytes.word_mapped source dst length index domain arena (by omega) aligned multiple)
    have bound : Zero.price length+1≤4 := by unfold Zero.price; omega
    omega
  · exact unaligned_call_cost source arguments dst length short aligned args (Zero.original_code source.code installed)

end InitECandidate.Solver.Input.ZeroShort

#print axioms InitECandidate.Solver.Input.ZeroShort.unaligned_body_cost
#print axioms InitECandidate.Solver.Input.ZeroShort.unaligned_call_cost
#print axioms InitECandidate.Solver.Input.ZeroShort.call_cost
