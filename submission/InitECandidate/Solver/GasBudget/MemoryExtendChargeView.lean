import InitECandidate.Solver.GasBudget.MemoryExtendCall
import InitECandidate.Solver.GasBudget.RegularChargeMemory

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem View.after_charge (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch amount : BitVec 64) (arguments : List (ExpHOL 64))
    (view : View source frame base length capacity pointer scratch)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)])
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") arguments) = (none, post)) :
    View post frame base length capacity pointer scratch := by
  have code := OriginalCodeEnvironment.charge_gas source.code view.installed
  obtain ⟨gas, used, positive, clock, gasMapped, usedMapped, gasCell, usedCell, affordable, frameEq, budget, debit, credit⟩ :=
    RegularCharge.call_normal source post frame amount arguments args code view.ev cap normal
  have cell (offset : BitVec 64) (notGas : offset ≠ 64#64) (notUsed : offset ≠ 184#64) :
      post.memory (frame + offset) = source.memory (frame + offset) :=
    RegularCharge.call_other_word source post frame amount (frame + offset) arguments args code view.ev cap normal
      (offsets_ne frame offset 64#64 notGas) (offsets_ne frame offset 184#64 notUsed)
  have baseCell := (cell 24#64 (by decide) (by decide)).trans view.baseCell
  have lengthCell := (cell 32#64 (by decide) (by decide)).trans view.lengthCell
  have capacityCell := (cell 40#64 (by decide) (by decide)).trans view.capacityCell
  rw [frameEq]
  exact ⟨view.installed, view.ev, view.mapped, baseCell, lengthCell, capacityCell,
    view.depth, view.slack, view.lengthAligned, view.capacityAligned, view.baseAligned, view.pointerGlobal,
    view.scratchGlobal, view.cursor, view.ordered, view.scratchAligned, view.frameAbove, view.frameFits, view.arena⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_charge
