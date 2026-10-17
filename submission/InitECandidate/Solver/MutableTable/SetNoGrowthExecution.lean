import InitECandidate.Solver.MutableTable.SetNoGrowthTail

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def noGrowthPrice (kind : KeyHash.Kind) (count : Nat) : Nat := Insert.findPrice kind count + Insert.rawPrice kind count

/-- Complete original setter body when its actual occupancy guard excludes
growth. All lookup/update/insert decisions and helper executions are derived.
Physical ownership/count/code/clock entry premises remain explicit. -/
theorem no_growth_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count value : BitVec 64) (bits : Nat) (items : List Nat)
    (data : Insert.GeneralData source table p kind vals order position count bits items)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word p.key)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (countBound : count.toNat ≤ items.length) (room : 2 * items.length + 2 ≤ 2 ^ bits)
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : noGrowthPrice kind items.length ≤ source.clock) :
    ∃ paid memory target, paid ≤ noGrowthPrice kind items.length ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      (memory (table + 24#64) = .word count ∨ memory (table + 24#64) = .word (count + 1#64)) ∧ Effect source kind p table vals order position count value memory := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", localVar "key"] = some [.val (.word table), .val (.word p.key)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tLocal, keyLocal]
  obtain ⟨findPaid, index, findBound, indexBound, callRun, selected⟩ := Insert.GeneralData.find_call source table p kind vals order position count bits items data
    memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args (by dsimp only [noGrowthPrice] at enough; omega)
  let resumed := WitnessRadix.QueryBranch.bind {source with clock := source.clock - findPaid} "i" index
  have resumedData := Insert.GeneralData.of_fields source resumed table p kind vals order position count bits items data rfl rfl rfl rfl
  obtain ⟨tailPaid, memory, post, tailBound, tailRun, tailFrame, countCell, effect⟩ := no_growth_tail resumed table p kind vals order position count value index bits items
    resumedData ((bind_lookup_other _ "i" "t" _ (by decide)).trans tLocal)
    ((bind_lookup_other _ "i" "key" _ (by decide)).trans keyLocal)
    ((bind_lookup_other _ "i" "value" _ (by decide)).trans valueLocal) (bind_lookup_same _ _ _)
    (Find.Selection.of_fields source resumed p index rfl rfl rfl selected) indexBound countBound room insertCode (by change Insert.rawPrice kind items.length ≤ source.clock - findPaid; dsimp only [noGrowthPrice] at enough; omega)
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex) =
    (let output := evaluateHOLFiniteState resumed afterIndex; (output.1, restore source "i" output.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨findPaid + tailPaid, memory, restore source "i" post, by dsimp only [noGrowthPrice] at enough ⊢; omega, ?_, ?_, ?_, Effect.of_fields resumed source kind p table vals order position count value memory rfl rfl rfl effect⟩
  · rw [body_shape]
    exact callRun
  · change emptyLocalsHOLFinite post = _
    rw [tailFrame]
    have clocks : source.clock - findPaid - tailPaid = source.clock - (findPaid + tailPaid) := by omega
    change emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - findPaid - tailPaid} = _
    rw [clocks]
  · by_cases same : index = p.capacity
    · exact Or.inr (by simpa only [if_pos same] using countCell)
    · exact Or.inl (by simpa only [if_neg same] using countCell)

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.no_growth_execute
