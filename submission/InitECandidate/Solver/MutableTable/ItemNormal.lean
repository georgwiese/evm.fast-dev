import InitECandidate.Solver.MutableTable.ItemExecution
import InitECandidate.Solver.ClockPadding
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.MutableTable.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_item") = some (formals,body,Slot.tripleShape) := by
  have checked := Input.OriginalCode.indexed code installed 130 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_item) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,ReadCall.formals,Slot.tripleShape,
    Guest.guestFn_htab_item,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem slot_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_slot") = some (Slot.formals,Slot.body,Slot.tripleShape) := by
  have checked := Input.OriginalCode.indexed code installed 129 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_slot) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Slot.body,Slot.formals,ReadCall.formals,Slot.tripleShape,
    Guest.guestFn_htab_slot,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (ordinal : Fin slots.length)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word (BitVec.ofNat 64 ordinal.val))))
    (slotCode : source.code.lookup (ofString "htab_slot") = some (Slot.formals,Slot.body,Slot.tripleShape))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),target)) :
    1 ≤ source.clock ∧ ∃ value, returned = Slot.triple 1#64
      (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  let padded := {source with clock := source.clock + 1}
  have paddedModel := MemoryModel.Occupied.of_fields source padded kind plan slots occupied rfl rfl rfl
  obtain ⟨value,post,actual,modelFrame⟩ := execute padded kind plan valid domain slots paddedModel header ordinal tableLocal ordinalLocal slotCode (by change 1 ≤ source.clock + 1; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) target 1
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + 1} = post at postEq
  have frame : emptyLocalsHOLFinite {target with clock := target.clock + 1} =
      emptyLocalsHOLFinite {source with clock := source.clock + 1 - 1} := by
    rw [postEq]
    exact modelFrame
  have stripped := InitECandidate.Solver.strip_clock_padding source target source 1 1 (by omega) frame
  exact ⟨stripped.1,value,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,stripped.2⟩

end InitECandidate.Solver.MutableTable.Item

#print axioms InitECandidate.Solver.MutableTable.Item.original_code
#print axioms InitECandidate.Solver.MutableTable.Item.slot_code
#print axioms InitECandidate.Solver.MutableTable.Item.body_normal
