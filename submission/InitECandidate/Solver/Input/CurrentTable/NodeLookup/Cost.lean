import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Program
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentTable.NodeLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem after_get_cost (code) : ClockCost.Bound code afterGet 0 :=
  ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code)) (ClockCost.returned code _)

theorem body_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code body := by
  rw [body_shape]
  apply LocalEffects.scoped_body code _ _ _ _ _ Get.formals Get.body Get.resultShape
    (Get.original_code code installed) (Get.body_readonly code installed)
  exact LocalEffects.sequence code _ _
    (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code)) (LocalEffects.returned code _)

/-- The unchanged database wrapper adds only its one lookup caller tick;
all record reads and present/absent branches are straight-line source work. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤264 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word table),.val (.word pointer)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,hashCell]
  obtain ⟨callee,called,tableCell,keyCell⟩ := word_pair_environment source.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    Get.body Get.resultShape table pointer (by decide) (Get.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have price := Get.body_cost entry (evaluateHOLFiniteState entry Get.body).2 table cap root pointer next count valid bits left right keys ValueOf
    (image.of_frame rfl) tableCell keyCell installed (evaluateHOLFiniteState entry Get.body).1 rfl
  rw [body_shape]
  exact ClockCost.scoped_current source (ofString "r") Get.resultShape (ofString "htab_get") arguments _ Get.body afterGet callee Get.resultShape
    263 0 args called price (after_get_cost source.code)

end InitECandidate.Solver.Input.CurrentTable.NodeLookup

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.body_readonly
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeLookup.body_cost
