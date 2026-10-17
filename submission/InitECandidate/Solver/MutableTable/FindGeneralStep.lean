import InitECandidate.Solver.MutableTable.FindStep32
import InitECandidate.Solver.MutableTable.KeyCompare

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual comparison arguments for either original mutable key width. -/
theorem general_comparison_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (kind : KeyHash.Kind) (locals : Locals source p index)
    (keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind)) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) comparisonArguments =
      some (KeyCompare.values kind (p.keys + index * p.stride) p.key) := by
  simp [evalListHOLFinite, comparisonArguments, keyAddress, evalListHOLExact, evalHOLExact, toExact,
    localVar, locals.keys, locals.index, locals.stride, locals.key, locals.klen, keyLength,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, KeyCompare.values, MemeqByteRuntime.values]

/-- One actual generic-width table-probe body. The real memeq call is derived from
mapped bytes for either alignment; its actual0/1answer selects return or the
literal masked increment. No logical-key or successful-comparator oracle. -/
theorem general_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (kind : KeyHash.Kind) (locals : Locals source p index)
    (keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind))
    (leftFits : (p.keys + index * p.stride).toNat + KeyHash.keySize kind < 2 ^ 64)
    (rightFits : p.key.toNat + KeyHash.keySize kind < 2 ^ 64)
    (leftMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress (p.keys + index * p.stride) offset)))
    (rightMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
      (WitnessRadix.byteAddress p.key offset)))
    (code : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (little : source.be = false)
    (enough : MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ (paid : Nat) (reply : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧ (reply = 0#64 ∨ reply = 1#64) ∧
      evaluateHOLFiniteState source loopBody = (if reply = 0#64 then none else some (.returned (.val (.word index))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} ∧
      (reply = 0#64 → target = WitnessRadix.QueryBranch.bind {source with clock := source.clock - paid} "i" (next p index)) := by
  obtain ⟨spent, reply, spentBound, replyBound, caller⟩ := KeyCompare.call_of_mapped source kind (p.keys + index * p.stride) p.key
    "eq" comparisonArguments afterEqual (general_comparison_arguments source p index kind locals keyLength) code
    leftFits rightFits leftMapped rightMapped little enough
  change spent ≤ MemeqByteRuntime.price (KeyHash.keySize kind) at spentBound
  let resumed := WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} "eq" reply
  have inResumed : Locals resumed p index :=
    ⟨(bind_lookup_other _ "eq" "cap" _ (by decide)).trans locals.cap,
     (bind_lookup_other _ "eq" "klen" _ (by decide)).trans locals.klen,
     (bind_lookup_other _ "eq" "stride" _ (by decide)).trans locals.stride,
     (bind_lookup_other _ "eq" "keys" _ (by decide)).trans locals.keys,
     (bind_lookup_other _ "eq" "used" _ (by decide)).trans locals.used,
     (bind_lookup_other _ "eq" "key" _ (by decide)).trans locals.key,
     (bind_lookup_other _ "eq" "i" _ (by decide)).trans locals.index⟩
  have tailRun := after_equal resumed p index reply inResumed (bind_lookup_same _ _ _)
  change evaluateHOLFiniteState source loopBody =
    (let output := evaluateHOLFiniteState resumed afterEqual
     (output.1, restore source "eq" output.2)) at caller
  rw [tailRun] at caller
  by_cases zero : reply = 0#64
  · rw [if_pos zero] at caller
    have restored : restore source "eq" (WitnessRadix.QueryBranch.bind resumed "i" (next p index)) =
        WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} "i" (next p index) := by
      rw [restore_bind_other _ _ "eq" "i" _ (by decide)]
      have back : restore source "eq" resumed = {source with clock := source.clock - (spent + 1)} :=
        restore_bound {source with clock := source.clock - (spent + 1)} "eq" reply
      rw [back]
    change evaluateHOLFiniteState source loopBody = (none, restore source "eq" (WitnessRadix.QueryBranch.bind resumed "i" (next p index))) at caller
    rw [restored] at caller
    refine ⟨spent + 1, reply, WitnessRadix.QueryBranch.bind {source with clock := source.clock - (spent + 1)} "i" (next p index), by omega, replyBound, ?_, rfl, ?_⟩
    · simpa only [if_pos zero] using caller
    · intro _; rfl
  · rw [if_neg zero] at caller
    refine ⟨spent + 1, reply, restore source "eq" (emptyLocalsHOLFinite resumed), by omega, replyBound, ?_, rfl, ?_⟩
    · simpa only [if_neg zero] using caller
    · intro impossible; exact False.elim (zero impossible)

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.general_comparison_arguments
#print axioms InitECandidate.Solver.MutableTable.Find.general_step
