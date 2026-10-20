import InitECandidate.Solver.Input.MainEvmProgram
import InitECandidate.Solver.Input.InitializerBytesFrame

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def systemStep (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) :=
  QueryBranch.bind {source with memory := ByteStore.put source.memory source.be (byteAddress pointer index) 255#8} "i" (BitVec.ofNat 64 (index + 1))
def systemWalk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 Guest.HostMemory
  | 0 => source
  | rounds + 1 => systemWalk (systemStep (decClockHOLFinite source) pointer index) pointer (index + 1) rounds

theorem system_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (bounded : index ≤ 20)
    (binding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    @evalHOLFinite 64 Guest.HostMemory _ source (fun address => Classical.propDecidable (source.memaddrs address)) (.cmp .less (.var .local (ofString "i")) (.const 20#64)) =
      some (.val (.word (if index < 20 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 index).toNat = index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sign : index < 2 ^ (64 - 1) := by omega
  simp [evalHOLFinite,evalHOLExact,toExact,binding,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,sign,show ¬ 9223372036854775808 ≤ index by omega]

theorem system_step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat)
    (pointerBinding : source.globals.lookup (ofString "vm_system_address") = some (.val (.word pointer)))
    (indexBinding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer index))) :
    evaluateHOLFiniteState source systemLoopBody = (none,systemStep source pointer index) := by
  have address : QueryBranch.eval source (.op .add [.var .global (ofString "vm_system_address"),.var .local (ofString "i")]) = some (.val (.word (byteAddress pointer index))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,pointerBinding,indexBinding,valueIsWord,valueWord,wordOpHOL,wordOp,byteAddress]
  have stored := ByteStore.execute source _ (.const 255#64) (byteAddress pointer index) 255#8 address rfl mapped
  let middle := {source with memory := ByteStore.put source.memory source.be (byteAddress pointer index) 255#8}
  have increment : QueryBranch.eval middle (.op .add [.var .local (ofString "i"),.const 1#64]) = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
    simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,middle,indexBinding,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have assigned := StateSteps.assign_execute middle "i" _ (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index + 1)) indexBinding increment
  rw [systemLoopBody,StateSteps.next_sequence source middle _ _ stored (Nat.le_refl _)]
  exact assigned

theorem system_loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat)
    (remaining : index + rounds = 20)
    (pointerBinding : source.globals.lookup (ofString "vm_system_address") = some (.val (.word pointer)))
    (indexBinding : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 24) (enough : rounds ≤ source.clock) :
    evaluateHOLFiniteState source systemLoop = (none,systemWalk source pointer index rounds) := by
  classical
  induction rounds generalizing source index with
  | zero =>
    have testRun := system_test_read source index (by omega) indexBinding
    have last : index = 20 := by omega
    simp only [last,show ¬ 20 < 20 from Nat.lt_irrefl _,if_neg] at testRun
    rw [systemLoop,evaluateHOLFiniteState_while_total,testRun]
    simp [systemWalk]
  | succ rounds ih =>
    let entry := decClockHOLFinite source
    let next := systemStep entry pointer index
    have bodyRun := system_step_execute entry pointer index pointerBinding indexBinding
      (AllocatedBytes.byte_mapped entry pointer 24 index domain arena (by omega))
    have currentIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
      simp [next,systemStep,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have currentPointer : next.globals.lookup (ofString "vm_system_address") = some (.val (.word pointer)) := pointerBinding
    have nextClock : next.clock = source.clock - 1 := rfl
    have following := ih next (index + 1) (by omega) currentPointer currentIndex domain (by rw [nextClock]; omega)
    have testRun := system_test_read source index (by omega) indexBinding
    simp only [if_pos (show index < 20 by omega)] at testRun
    rw [systemLoop,evaluateHOLFiniteState_while_total,testRun]
    simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide,↓reduceIte,if_neg (show source.clock ≠ 0 by omega)]
    rw [bodyRun,StateSteps.fixed_clock entry next none (by rw [nextClock]; exact Nat.le_refl _)]
    exact following

theorem system_walk_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (systemWalk source pointer index rounds).clock = source.clock - rounds := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    rw [systemWalk,ih]
    change source.clock - 1 - rounds = source.clock - (rounds + 1)
    omega

theorem system_walk_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    InitializerAllocations.context (systemWalk source pointer index rounds) = InitializerAllocations.context source := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact (ih (systemStep (decClockHOLFinite source) pointer index) (index + 1)).trans rfl

theorem system_walk_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    (systemWalk source pointer index rounds).globals = source.globals := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact ih (systemStep (decClockHOLFinite source) pointer index) (index + 1)

theorem system_walk_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds : Nat) :
    KeccakAbsorb.hashControl (systemWalk source pointer index rounds) = KeccakAbsorb.hashControl source := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih => exact (ih (systemStep (decClockHOLFinite source) pointer index) (index + 1)).trans rfl

theorem system_walk_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index rounds : Nat)
    (away : ∀ position,index ≤ position → position < index + rounds → query ≠ panByteAlignHOL (width := 64) (byteAddress pointer position)) :
    (systemWalk source pointer index rounds).memory query = source.memory query := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    exact (ih (systemStep (decClockHOLFinite source) pointer index) (index + 1) (by intro position low high; exact away position (by omega) (by omega))).trans
      (ByteStore.away source.memory source.be (byteAddress pointer index) query 255#8 (away index (Nat.le_refl _) (by omega)))

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_test_read
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_step_execute
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_loop_execute
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_walk_clock
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_walk_context
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_walk_globals
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_walk_control
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.system_walk_away
