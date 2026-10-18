import InitECandidate.Solver.GasBudget.RootMessageProgram

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- Both real post-MSG_GAS stores, including the actual four-word value
load/store. Their successful reads/maps are derived from normal execution;
the gas cell and every object outside the176byte message are retained. -/
theorem stores_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (start : Nat) (reservoir : BitVec 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (reservoirLocal : source.locals.lookup (ofString "reservoir") = some (.val (.word reservoir)))
    (normal : evaluateHOLFiniteState source RootCaller.afterMsgGas = (some (.returned value), post)) :
    ∃ ready : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState ready WarmPrecompiles.constructorSite = (some (.returned value), post) ∧
      ready = {source with memory := ready.memory} ∧
      ready.memory (BitVec.ofNat 64 start + 40#64) = source.memory (BitVec.ofNat 64 start + 40#64) ∧
      ∀ query : BitVec 64, query.toNat < start ∨ start + 176 ≤ query.toNat → ready.memory query = source.memory query := by
  rw [after_gas_shape] at normal
  have reservoirSafe : Input.LocalPrefix (ofString "m") reservoirStore := .store _ _
  obtain ⟨stored, storeRun, afterReservoir, _⟩ := reservoirSafe.normal_continue source post _ value normal
  have reservoirRead : eval source (localVar "reservoir") = some (.val (.word reservoir)) := by simp [eval, localVar, evalHOLExact, toExact, reservoirLocal]
  have reservoirWidth (actual : ValueHOL 64) (read : eval source (localVar "reservoir") = some actual) : (flattenHOL actual).length ≤ 1 := by
    have same : actual = .val (.word reservoir) := Option.some.inj (read.symm.trans reservoirRead)
    rw [same]
    simp [flattenHOL]
  obtain ⟨storedFrame, firstOutside, firstGas⟩ := MessageField.normal_frame source stored start 48 1 (localVar "reservoir") region (by decide) messageLocal reservoirWidth storeRun
  have storedMessage : stored.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [storedFrame]; exact messageLocal
  have valueSafe : Input.LocalPrefix (ofString "m") valueStore := .store _ _
  obtain ⟨ready, valueRun, afterValue, _⟩ := valueSafe.normal_continue stored post _ value afterReservoir
  have valueWidth (actual : ValueHOL 64) (read : eval stored valueExpression = some actual) : (flattenHOL actual).length ≤ 4 :=
    Nat.le_of_eq (Input.load4_length stored _ actual read)
  obtain ⟨readyFrame, secondOutside, secondGas⟩ := MessageField.normal_frame stored ready start 56 4 valueExpression region (by decide) storedMessage valueWidth valueRun
  have composite := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := ready.memory}) storedFrame
  have frame : ready = {source with memory := ready.memory} := readyFrame.trans composite
  refine ⟨ready, afterValue, frame, (secondGas 40 (by decide) (Or.inl (by decide))).trans (firstGas 40 (by decide) (Or.inl (by decide))), ?_⟩
  intro query outside
  exact (secondOutside query outside).trans (firstOutside query outside)

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.stores_normal
