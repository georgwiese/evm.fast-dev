import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_new with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "key_len",.one),(ofString "cap",.one)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_new")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 116 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_new,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
/-- The actual Patricia table constructor has four persistent allocation
calls and no initialization loops. All guards, stores and failures are
covered; allocator room and normal stores are not assumed. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body 8 := by
  simp only [body,Guest.Software.guestFn_htab_new,progToHOL,shapeToHOL]
  apply WitnessRadix.PersistentAlloc.scoped_price (tailPrice:=6) code installed
  apply ClockCost.declared
  apply ClockCost.declared
  apply ClockCost.sequence (firstPrice:=0) (secondPrice:=6)
  · exact ClockCost.conditional code _ _ _ 0 0 (ClockCost.assign code _ _) (ClockCost.skip code)
  · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=6)
    · exact ClockCost.store code _ _
    · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=6)
      · exact ClockCost.store code _ _
      · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=6)
        · exact ClockCost.store code _ _
        · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=6)
          · exact ClockCost.store code _ _
          · apply WitnessRadix.PersistentAlloc.scoped_price (tailPrice:=4) code installed
            apply ClockCost.sequence (firstPrice:=0) (secondPrice:=4)
            · exact ClockCost.store code _ _
            · apply WitnessRadix.PersistentAlloc.scoped_price (tailPrice:=2) code installed
              apply ClockCost.sequence (firstPrice:=0) (secondPrice:=2)
              · exact ClockCost.store code _ _
              · apply WitnessRadix.PersistentAlloc.scoped_price (tailPrice:=0) code installed
                apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
                · exact ClockCost.store code _ _
                · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
                  · exact ClockCost.store code _ _
                  · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
                    · exact ClockCost.store code _ _
                    · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
                      · exact ClockCost.store code _ _
                      · apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
                        · exact ClockCost.store code _ _
                        · exact ClockCost.returned code _

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.original_code
#print axioms InitECandidate.Solver.Input.CurrentTable.New.body_cost
