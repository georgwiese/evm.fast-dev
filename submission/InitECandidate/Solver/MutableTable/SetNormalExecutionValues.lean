import InitECandidate.Solver.MutableTable.SetModelTailValues
import InitECandidate.Solver.MutableTable.SetModelExecution
import InitECandidate.Solver.MutableTable.SetNormalGrowthRoom

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal original setter derives allocation room only if it reaches
actual growth. This funded intermediate theorem retains the complete
physical model, footprint and price, without prospective layout validity. -/
theorem model_execute_normal_values (source actualTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (query value : BitVec 64)
    (property : BitVec 64 → Prop)
    (values : Get.OccupiedValuesHave source (cell old .values 0) (BitVec.ofNat 64 old.capacity) slots property)
    (owned : property value)
    (bits : Nat) (small : bits < 64) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query))) (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (actualValue : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned actualValue), actualTarget))
    (enough : modelPrice kind old.capacity slots.length ≤ source.clock) :
    ∃ paid globals memory plan next, paid ≤ modelPrice kind old.capacity slots.length ∧
      (plan = old → paid ≤ noGrowthPrice kind slots.length) ∧ actualValue = .val (.word 0#64) ∧
      ModelPost source kind old start slots.length paid globals memory actualTarget plan next ∧ Valid kind plan ∧
      Get.OccupiedValuesHave actualTarget (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) next property := by
  let p := parameters kind old query
  have data := MemoryModel.runtime_data source kind old oldValid domain query slots room header occupied bits small power queryFits queryMapped little hashCode copyCode
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (cell old .header 0)), .val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal, keyLocal]
  obtain ⟨findPaid, index, findBound, indexBound, callRun, selected⟩ := Insert.GeneralData.find_call source (cell old .header 0) p kind
    (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) bits slots data memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args
    (by dsimp only [modelPrice] at enough; omega)
  let resumed := WitnessRadix.QueryBranch.bind {source with clock := source.clock - findPaid} "i" index
  have expanded := normal
  rw [body_shape] at expanded
  have compared := callRun.symm.trans expanded
  have tailResult := congrArg Prod.fst compared
  change (evaluateHOLFiniteState resumed afterIndex).1 = some (.returned actualValue) at tailResult
  have tailNormal : evaluateHOLFiniteState resumed afterIndex = (some (.returned actualValue), (evaluateHOLFiniteState resumed afterIndex).2) := Prod.ext tailResult rfl
  have resumedT : resumed.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))) := (bind_lookup_other _ "i" "t" _ (by decide)).trans tableLocal
  have needed : resumed.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 old.capacity))) →
      old.capacity < 2 * slots.length + 2 → Valid kind (relocated kind (old.base .header) start (2 * old.capacity)) := by
    intro absent threshold
    exact growth_layout_of_normal_tail resumed (evaluateHOLFiniteState resumed afterIndex).2 kind old oldValid start slots.length startBound startAligned earlier domain
      (MemoryModel.Occupied.length_le source kind old slots occupied) header resumedT absent threshold heap allocCode trapCode growCode actualValue tailNormal
  have resumedData := Insert.GeneralData.of_fields source resumed (cell old .header 0) p kind
    (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) bits slots data rfl rfl rfl rfl
  have resumedModel := MemoryModel.Occupied.of_fields source resumed kind old slots occupied rfl rfl rfl
  obtain ⟨tailPaid, globals, memory, post, plan, next, tailBound, tailOldBound, tailRun, tailPost, nextValid, nextValues⟩ :=
    model_tail_values resumed kind old oldValid start earlier domain little slots needed room header resumedModel query value index property values owned bits small power minimum resumedData resumedT
      ((bind_lookup_other _ "i" "key" _ (by decide)).trans keyLocal) ((bind_lookup_other _ "i" "value" _ (by decide)).trans valueLocal) (bind_lookup_same _ _ _)
      (Find.Selection.of_fields source resumed p index rfl rfl rfl selected) indexBound heap allocCode zeroCode insertCode growCode
      (by change afterGrowPrice kind old.capacity slots.length ≤ source.clock - findPaid; dsimp only [modelPrice] at enough; omega)
  rw [tailRun] at callRun
  have actual : evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), restore source "i" post) := by
    rw [body_shape]
    exact callRun
  have agree := normal.symm.trans actual
  have resultEq := congrArg Prod.fst agree
  have targetEq := congrArg Prod.snd agree
  change actualTarget = restore source "i" post at targetEq
  refine ⟨findPaid + tailPaid, globals, memory, plan, next, ?_, ?_, ?_, ?_, nextValid, ?_⟩
  · dsimp only [modelPrice]
    omega
  · intro same
    have bounded := tailOldBound same
    dsimp only [noGrowthPrice]
    omega
  · simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  · rw [targetEq]
    refine ⟨?_, tailPost.shape, tailPost.countBound, tailPost.grew, tailPost.half, tailPost.header,
      MemoryModel.Occupied.of_fields post (restore source "i" post) kind plan next tailPost.occupied rfl rfl rfl, tailPost.footprint⟩
    change emptyLocalsHOLFinite post = _
    rw [tailPost.frame]
    change emptyLocalsHOLFinite {source with globals := globals, memory := memory, clock := source.clock - findPaid - tailPaid} = _
    rw [Nat.sub_sub]

  · rw [targetEq]
    exact nextValues

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_execute_normal_values
