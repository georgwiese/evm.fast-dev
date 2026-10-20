import InitECandidate.Solver.Input.BnModmulExecution

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Facts about the current, already initialized arithmetic buffer. -/
structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : Prop where
  installed : OriginalCode.Installed source.code
  params : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer))
  a : source.globals.lookup (ofString "bn_accel_a") = some (.val (.word pointer))
  b : source.globals.lookup (ofString "bn_accel_b") = some (.val (.word (pointer + 32#64)))
  d : source.globals.lookup (ofString "bn_accel_d") = some (.val (.word (pointer + 128#64)))
  oracle : source.ffi.oracle = InitE.sourceOracle
  domain : source.memaddrs = InitE.ordinaryDomain
  arena : AllocatedBytes.Arena pointer 160
  aligned : pointer.toNat % 8 = 0
  little : source.be = false
  modulus : ∀ index : Fin 4,source.memory (byteAddress pointer (96 + 8 * index.val)) = .word (Main.BnAccelInitialization.modulus index)

noncomputable def bodyPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words) :=
  reply (operands {source with clock := source.clock - 1} pointer a b) pointer

noncomputable def bodyResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words) : Words :=
  result (operands {source with clock := source.clock - 1} pointer a b) pointer

/-- Full original593 body, including its real initialization guard call,
operand stores, external event and current result load. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (entry : Environment source pointer)
    (aLocal : source.locals.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a))
    (bLocal : source.locals.lookup (ofString "b") = some (RlpWrite.U256Value.tuple b)) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (some (.returned (RlpWrite.U256Value.tuple (bodyResult source pointer a b))),emptyLocalsHOLFinite (bodyPost source pointer a b)) := by
  have nonzero : pointer ≠ 0#64 := by
    intro zero
    have lower := entry.arena.lower
    rw [zero] at lower
    contradiction
  have initialized := Main.BnAccelInitialization.initialized_call source pointer entry.installed entry.params nonzero enough
  let ready := {source with clock := source.clock - 1}
  have stored := stores_execute ready pointer a b entry.a entry.b aLocal bLocal entry.domain entry.arena entry.aligned
  have modulus (index : Fin 4) : (operands ready pointer a b).memory (byteAddress pointer (96 + 8 * index.val)) = .word (Main.BnAccelInitialization.modulus index) := by
    rw [operands_prefix ready pointer a b (96 + 8 * index.val) (by omega) (by omega)]
    exact entry.modulus index
  have called := after_stores_execute (operands ready pointer a b) pointer entry.params entry.d entry.oracle entry.domain entry.arena entry.aligned entry.little modulus
  rw [body_shape,StateSteps.next_sequence source ready initialization _ initialized (by dsimp [ready]; omega),stored]
  exact called

/-- The full body leaves every non-result prefix word unchanged except the
explicit operand stores. This supplies the next call's actual modulus. -/
theorem body_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (entry : Environment source pointer) (offset : Nat) (lower : 64 ≤ offset) (upper : offset < 128) :
    (bodyPost source pointer a b).memory (byteAddress pointer offset) = source.memory (byteAddress pointer offset) := by
  let ready := {source with clock := source.clock - 1}
  exact (reply_prefix (operands ready pointer a b) pointer entry.domain entry.arena entry.aligned entry.little offset upper).trans
    (operands_prefix ready pointer a b offset lower upper)

theorem body_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b : Words)
    (entry : Environment source pointer) : Environment (bodyPost source pointer a b) pointer := by
  refine ⟨entry.installed,entry.params,entry.a,entry.b,entry.d,entry.oracle,entry.domain,entry.arena,entry.aligned,entry.little,?_⟩
  intro index
  rw [body_prefix source pointer a b entry (96 + 8 * index.val) (by omega) (by omega)]
  exact entry.modulus index

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.execute
#print axioms InitECandidate.Solver.Input.BnModmul.body_prefix
#print axioms InitECandidate.Solver.Input.BnModmul.body_environment
