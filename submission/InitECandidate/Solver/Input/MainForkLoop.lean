import InitECandidate.Solver.Input.MainForkProgram
import InitECandidate.Solver.Input.InitializerBytesFrame

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def addressStep (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) :=
  QueryBranch.bind {source with memory := ByteStore.put source.memory source.be (byteAddress pointer (20 * index + 19)) (BitVec.ofNat 8 (index + 1))} "i" (BitVec.ofNat 64 (index + 1))
def addressWalk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 Guest.HostMemory
  | 0 => source
  | rounds + 1 => addressWalk (addressStep (decClockHOLFinite source) pointer index) pointer (index + 1) rounds

theorem address_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (bounded : index ≤ 17)
    (binding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) (.cmp .less (.var .local (ofString "i")) (.const 17#64)) =
      some (.val (.word (if index < 17 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 index).toNat = index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sign : index < 2 ^ (64 - 1) := by omega
  simp [evalHOLFinite,evalHOLExact,toExact,binding,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,sign,show ¬ 9223372036854775808 ≤ index by omega]

theorem address_step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) (bounded : index < 17)
    (pointerBinding : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word pointer)))
    (indexBinding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer (20 * index + 19)))) :
    evaluateHOLFiniteState source loopBody = (none,addressStep source pointer index) := by
  have byteNumber : (BitVec.ofNat 8 (index + 1)).toNat = index + 1 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have destination : QueryBranch.eval source (.op .add [.var .global (ofString "precompile_addrs"),.panop .mul [.var .local (ofString "i"),.const 20#64],.const 19#64]) =
      some (.val (.word (byteAddress pointer (20 * index + 19)))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,pointerBinding,indexBinding,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      byteAddress,← BitVec.ofNat_mul,← BitVec.ofNat_add,Nat.mul_comm]
  have valueRead : QueryBranch.eval source (.op .add [.var .local (ofString "i"),.const 1#64]) = some (.val (.word (BitVec.ofNat 64 (BitVec.ofNat 8 (index + 1)).toNat))) := by
    rw [byteNumber]
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,indexBinding,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have stored := ByteStore.execute source _ _ (byteAddress pointer (20 * index + 19)) (BitVec.ofNat 8 (index + 1)) destination valueRead mapped
  let middle := {source with memory := ByteStore.put source.memory source.be (byteAddress pointer (20 * index + 19)) (BitVec.ofNat 8 (index + 1))}
  have increment : QueryBranch.eval middle (.op .add [.var .local (ofString "i"),.const 1#64]) = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,middle,indexBinding,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have assigned := StateSteps.assign_execute middle "i" _ (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index + 1)) indexBinding increment
  rw [loopBody,StateSteps.next_sequence source middle _ _ stored (Nat.le_refl _)]
  exact assigned

theorem address_loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (remaining : index + rounds = 17)
    (pointerBinding : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word pointer)))
    (indexBinding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 360) (enough : rounds ≤ source.clock) :
    evaluateHOLFiniteState source loop = (none,addressWalk source pointer index rounds) := by
  classical
  induction rounds generalizing source index with
  | zero =>
    have testRun := address_test_read source index (by omega) indexBinding
    have last : index = 17 := by omega
    simp only [last,show ¬ 17 < 17 from Nat.lt_irrefl _,if_neg] at testRun
    rw [loop,evaluateHOLFiniteState_while_total,testRun]
    simp [addressWalk]
  | succ rounds ih =>
    let entry := decClockHOLFinite source
    let next := addressStep entry pointer index
    have bodyRun := address_step_execute entry pointer index (by omega) pointerBinding indexBinding
      (AllocatedBytes.byte_mapped entry pointer 360 (20 * index + 19) domain arena (by omega))
    have currentIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
      simp [next,addressStep,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have currentPointer : next.globals.lookup (ofString "precompile_addrs") = some (.val (.word pointer)) := pointerBinding
    have nextClock : next.clock = source.clock - 1 := rfl
    have following := ih next (index + 1) (by omega) currentPointer currentIndex domain (by rw [nextClock]; omega)
    have testRun := address_test_read source index (by omega) indexBinding
    simp only [if_pos (show index < 17 by omega)] at testRun
    rw [loop,evaluateHOLFiniteState_while_total,testRun]
    simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide,↓reduceIte,if_neg (show source.clock ≠ 0 by omega)]
    rw [bodyRun,StateSteps.fixed_clock entry next none (by rw [nextClock]; exact Nat.le_refl _)]
    exact following

theorem address_walk_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (addressWalk source pointer index rounds).clock = source.clock - rounds := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    rw [addressWalk,ih]
    change source.clock - 1 - rounds = source.clock - (rounds + 1)
    omega

theorem address_walk_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    InitializerAllocations.context (addressWalk source pointer index rounds) = InitializerAllocations.context source := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact (ih (addressStep (decClockHOLFinite source) pointer index) (index + 1)).trans rfl

theorem address_walk_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (addressWalk source pointer index rounds).globals = source.globals := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact ih (addressStep (decClockHOLFinite source) pointer index) (index + 1)

theorem address_walk_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    KeccakAbsorb.hashControl (addressWalk source pointer index rounds) = KeccakAbsorb.hashControl source := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact (ih (addressStep (decClockHOLFinite source) pointer index) (index + 1)).trans rfl

theorem address_walk_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index rounds : Nat)
    (away : ∀ position,index ≤ position → position < index + rounds → query ≠ panByteAlignHOL (width := 64) (byteAddress pointer (20 * position + 19))) :
    (addressWalk source pointer index rounds).memory query = source.memory query := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    exact (ih (addressStep (decClockHOLFinite source) pointer index) (index + 1) (by intro position low high; exact away position (by omega) (by omega))).trans
      (ByteStore.away source.memory source.be (byteAddress pointer (20 * index + 19)) query (BitVec.ofNat 8 (index + 1)) (away index (Nat.le_refl _) (by omega)))

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_test_read
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_step_execute
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_loop_execute
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_walk_clock
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_walk_context
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_walk_globals
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_walk_control
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.address_walk_away
