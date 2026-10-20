import InitECandidate.Solver.Input.BnModmulMemory

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

/-- Current memory mapping supplies every actual quad access in the buffer. -/
theorem quad_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 160)
    (aligned : pointer.toNat % 8 = 0) (offsetAligned : offset % 8 = 0) (inside : offset + 32 ≤ 160) :
    ∀ index : Fin 4,source.memaddrs (pointer + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * index.val)) := by
  intro index
  have mapped := AllocatedBytes.word_mapped source pointer 160 (offset + 8 * index.val) domain arena (by omega) aligned (by omega)
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using mapped

/-- Two real stores precede the real external call. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (aBinding : source.globals.lookup (ofString "bn_accel_a") = some (.val (.word pointer)))
    (bBinding : source.globals.lookup (ofString "bn_accel_b") = some (.val (.word (pointer + 32#64))))
    (aRead : source.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a))
    (bRead : source.locals.lookup (ofString "b") = some (RlpWrite.U256Value.tuple b))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 160) (aligned : pointer.toNat % 8 = 0) :
    evaluateHOLFiniteState source afterInitialization = evaluateHOLFiniteState (operands source pointer a b) afterStores := by
  have mappedA := quad_mapped source pointer 0 domain arena aligned (by decide) (by decide)
  have first := RlpWrite.U256Value.store_execute source (.var .global (ofString "bn_accel_a")) (.var .local (ofString "a")) pointer a aBinding aRead (by simpa using mappedA)
  let middle := {source with memory := WordWrites.write source.memory (RlpWrite.U256Value.wordWrites pointer a)}
  have second := RlpWrite.U256Value.store_execute middle (.var .global (ofString "bn_accel_b")) (.var .local (ofString "b")) (pointer + 32#64) b bBinding bRead
    (quad_mapped middle pointer 32 domain arena aligned (by decide) (by decide))
  unfold afterInitialization
  rw [StateSteps.next_sequence source middle storeA _ first (Nat.le_refl _),
    StateSteps.next_sequence middle (operands source pointer a b) storeB _ second (Nat.le_refl _)]

noncomputable def reply (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) :=
  BnArithmetic.post source pointer (inputWords source pointer)

noncomputable def result (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : Words :=
  RlpWrite.U256Value.memoryWords (reply source pointer) (pointer + 128#64)

/-- The genuine external call and actual return load execute from the current
buffer. The returned tuple is read from the real reply memory. -/
theorem after_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (params : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer)))
    (dBinding : source.globals.lookup (ofString "bn_accel_d") = some (.val (.word (pointer + 128#64))))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle) (domain : source.memaddrs = InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena pointer 160) (aligned : pointer.toNat % 8 = 0) (little : source.be = false)
    (modulus : ∀ index : Fin 4,source.memory (byteAddress pointer (96 + 8 * index.val)) = .word (Main.BnAccelInitialization.modulus index)) :
    evaluateHOLFiniteState source afterStores =
      (some (.returned (RlpWrite.U256Value.tuple (result source pointer))),emptyLocalsHOLFinite (reply source pointer)) := by
  have fits : pointer.toNat + 160 < 2 ^ 64 := by have := arena.upper; omega
  have mapped : ∀ index : Fin 20,source.memaddrs (byteAddress pointer (8 * index.val)) := by
    intro index
    exact AllocatedBytes.word_mapped source pointer 160 (8 * index.val) domain arena (by omega) aligned (by omega)
  have called := BnArithmetic.external_execute source pointer (inputWords source pointer) params oracleEq (input_length source pointer)
    (input_modulus source pointer modulus) (read_input source pointer aligned fits little mapped)
  have loaded := RlpWrite.U256Value.load (reply source pointer) (.var .global (ofString "bn_accel_d")) (pointer + 128#64) dBinding
    (quad_mapped (reply source pointer) pointer 128 domain arena aligned (by decide) (by decide))
  rw [afterStores,StateSteps.next_sequence source (reply source pointer) external returned called (Nat.le_refl _)]
  rw [returned,evaluateHOLFiniteState_return]
  simp only [eval] at loaded
  rw [loaded]
  simp [RlpWrite.U256Value.tuple,shapeOfHOLExact,sizeOfShapeWithContextHOL,sizeOfShapesWithContextHOL,result]

/-- The actual reply preserves all current words before its result quad. -/
theorem reply_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 160)
    (aligned : pointer.toNat % 8 = 0) (little : source.be = false) (offset : Nat) (inside : offset < 128) :
    (reply source pointer).memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  exact BnArithmetic.prefix_memory source pointer (inputWords source pointer) (input_length source pointer) aligned
    (by have := arena.upper; omega) little
    (by
      intro index
      have bound : index.val < 20 := by simpa only [input_length] using index.isLt
      exact AllocatedBytes.word_mapped source pointer 160 (8 * index.val) domain arena (by omega) aligned (by omega))
    (input_stored source pointer) offset inside

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.quad_mapped
#print axioms InitECandidate.Solver.Input.BnModmul.stores_execute
#print axioms InitECandidate.Solver.Input.BnModmul.after_stores_execute
#print axioms InitECandidate.Solver.Input.BnModmul.reply_prefix
