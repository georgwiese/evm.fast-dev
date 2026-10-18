import InitECandidate.Solver.GasBudget.OpcodeChargeLift
import InitECandidate.Solver.GasBudget.OpcodeChargeInstalled

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine positive first-charge event at a reached source state, with
exact paid call/loop clocks and the physical pre-suffix memory frame. -/
structure ChargeEvent (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) (paid amount : Nat) : Prop where
  fits : paid ≤ source.clock
  clock : ready.clock = source.clock - paid
  fields : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := ready.clock}
  budget : regularBudget ready.memory frame = regularBudget source.memory frame
  credit : (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + amount
  positive : 0 < amount
  outside : ∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 →
    ready.memory address = source.memory address

theorem ChargeEvent.prepend {source middle ready : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {first paid amount : Nat}
    (prior : StackPop.PrefixEffect source middle frame first) (event : ChargeEvent middle ready frame paid amount) :
    ChargeEvent source ready frame (first + paid) amount := by
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) prior.fields
  refine ⟨?_, ?_, event.fields.trans lift, event.budget.trans prior.budget, ?_, event.positive, ?_⟩
  · have a := prior.fits
    have b := event.fits
    rw [prior.clock] at b
    omega
  · rw [event.clock, prior.clock]
    omega
  · rw [event.credit]
    simp only [wordAt, prior.used]
  · intro address notSP notGas notUsed
    exact (event.outside address notSP notGas notUsed).trans (prior.outside address notSP)

theorem OpcodeChargeSites.fee_word (kind : OpcodeChargeSites.Kind) : (BitVec.ofNat 64 kind.fee).toNat = kind.fee := by
  cases kind <;> decide

theorem OpcodeChargeSites.fee_positive_nat (kind : OpcodeChargeSites.Kind) : 0 < kind.fee := by
  have positive := OpcodeChargeSites.fee_positive kind
  rw [OpcodeChargeSites.fee_word] at positive
  exact positive

theorem ChargeEvent.of_effect {source ready : PanSemStateFiniteExact 64 Guest.HostMemory} {frame sp remaining : BitVec 64}
    (kind : OpcodeChargeSites.Kind) {overhead : Nat}
    (effect : OpcodeChargePrefix.ChargedEffect source ready frame sp remaining kind.names.length (BitVec.ofNat 64 kind.fee) overhead) :
    ChargeEvent source ready frame (kind.names.length + 1 + overhead) kind.fee := by
  have credit := effect.used
  rw [OpcodeChargeSites.fee_word] at credit
  exact ⟨effect.fits, effect.clock, effect.fields, effect.budget, credit, OpcodeChargeSites.fee_positive_nat kind, effect.outside⟩

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.ChargeEvent.prepend
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.fee_word
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.fee_positive_nat
#print axioms InitECandidate.Solver.GasBudget.ChargeEvent.of_effect
