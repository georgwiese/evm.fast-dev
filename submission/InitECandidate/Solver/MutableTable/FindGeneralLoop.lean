import InitECandidate.Solver.MutableTable.FindGeneralChain

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 5000 in
/-- Actual generic-width probe loop and final absent-cap return. Every comparator
is the real uniform mapped caller. A physical occupied prefix of lengthD
costs at most(price(width)+2)*D source clocks respectively, without a hash distribution
or key-equality assumption. Construction/order invariants must supply D. -/
theorem general_chain_execute (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (kind : KeyHash.Kind) (index : BitVec 64) (length : Nat) (chain : GeneralChain snapshot p kind index length)
    (keyLength : p.keyLength = BitVec.ofNat 64 (KeyHash.keySize kind))
    (queryFits : p.key.toNat + KeyHash.keySize kind < 2 ^ 64)
    (little : snapshot.be = false)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : Locals source p index)
    (memory : snapshot.memory = source.memory) (domain : snapshot.memaddrs = source.memaddrs) (endian : snapshot.be = source.be)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress p.key offset)))
    (code : source.code.lookup (ofString "memeq") = some (WitnessRadix.Memeq32.formals, WitnessRadix.Memeq32.body, .one))
    (enough : generalProbePrice kind * length ≤ source.clock) :
    ∃ (paid : Nat) (answer : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ generalProbePrice kind * length ∧ answer.toNat ≤ p.capacity.toNat ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word answer))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  induction chain generalizing source with
  | empty index inside loaded =>
    have actual : usedByte source p index = some 0 := by
      rw [← usedByte_of_fields snapshot source p index memory domain endian]
      exact loaded
    have test : eval source condition = some (.val (.word 0#64)) := by
      simpa using condition_read source p index locals 0 actual
    have returned : evaluateHOLFiniteState source (.return (localVar "cap")) =
        (some (.returned (.val (.word p.capacity))), emptyLocalsHOLFinite source) := by
      simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, locals.cap, shapeOfHOLExact]
    refine ⟨0, p.capacity, emptyLocalsHOLFinite source, by simp, Nat.le_refl _, ?_, by simp only [Nat.sub_zero, emptyLocalsHOLFinite]⟩
    rw [afterIndex, loop, MemeqByteRuntime.loop_stop source condition loopBody (.return (localVar "cap")) test]
    exact returned
  | occupied index byte length inside nonzero loaded fits mapped tail ih =>
    have funded : (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * length +
        (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) ≤ source.clock := by
      change (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * (length + 1) ≤ source.clock at enough
      simpa only [Nat.mul_add, Nat.mul_one] using enough
    have positive : source.clock ≠ 0 := by omega
    have byteNonzero : byte.toNat ≠ 0 := by
      intro zero
      apply nonzero
      apply UInt8.toNat.inj
      exact zero
    have actual : usedByte source p index = some byte := by
      rw [← usedByte_of_fields snapshot source p index memory domain endian]
      exact loaded
    have test : eval source condition = some (.val (.word 1#64)) := by
      simpa only [if_neg byteNonzero] using condition_read source p index locals byte actual
    let entry := decClockHOLFinite source
    have entryLocals : Locals entry p index :=
      ⟨locals.cap, locals.klen, locals.stride, locals.keys, locals.used, locals.key, locals.index⟩
    have mappedSource : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64)
        (WitnessRadix.byteAddress (p.keys + index * p.stride) offset)) := by
      intro offset offsetInside
      rw [← domain]
      exact mapped offset offsetInside
    obtain ⟨stepPaid, reply, post, stepBound, replyBound, stepRun, stepFrame, advance⟩ := general_step entry p index kind entryLocals
      keyLength fits queryFits mappedSource queryMapped code (endian.symm.trans little) (by change MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock - 1; omega)
    have stepClock := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.clock) stepFrame
    change post.clock = source.clock - 1 - stepPaid at stepClock
    by_cases zero : reply = 0#64
    · rw [if_pos zero, advance zero] at stepRun
      let nextState := WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1 - stepPaid} "i" (next p index)
      change evaluateHOLFiniteState entry loopBody = (none, nextState) at stepRun
      have nextLocals : Locals nextState p (next p index) :=
        ⟨(bind_lookup_other _ "i" "cap" _ (by decide)).trans locals.cap,
         (bind_lookup_other _ "i" "klen" _ (by decide)).trans locals.klen,
         (bind_lookup_other _ "i" "stride" _ (by decide)).trans locals.stride,
         (bind_lookup_other _ "i" "keys" _ (by decide)).trans locals.keys,
         (bind_lookup_other _ "i" "used" _ (by decide)).trans locals.used,
         (bind_lookup_other _ "i" "key" _ (by decide)).trans locals.key,
         bind_lookup_same _ _ _⟩
      obtain ⟨paid, answer, target, paidBound, answerBound, tailRun, frame⟩ := ih nextState nextLocals memory domain endian queryMapped code
        (by change (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * length ≤ source.clock - 1 - stepPaid; omega)
      change paid ≤ (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * length at paidBound
      have step := MemeqByteRuntime.loop_continue source nextState condition loopBody (.return (localVar "cap")) test positive stepRun
        (by change source.clock - 1 - stepPaid ≤ source.clock - 1; omega)
      change evaluateHOLFiniteState source afterIndex = evaluateHOLFiniteState nextState afterIndex at step
      rw [tailRun] at step
      refine ⟨paid + stepPaid + 1, answer, target, ?_, answerBound, step, ?_⟩
      · change paid + stepPaid + 1 ≤ (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * (length + 1)
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · have clocks : source.clock - 1 - stepPaid - paid = source.clock - (paid + stepPaid + 1) := by omega
        change emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1 - stepPaid - paid} at frame
        rw [clocks] at frame
        exact frame
    · rw [if_neg zero] at stepRun
      have step := MemeqByteRuntime.loop_return source post condition loopBody (.return (localVar "cap")) index test positive stepRun
        (by omega)
      refine ⟨stepPaid + 1, index, post, ?_, by omega, step, ?_⟩
      · change stepPaid + 1 ≤ (MemeqByteRuntime.price (KeyHash.keySize kind) + 2) * (length + 1)
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · have clocks : source.clock - 1 - stepPaid = source.clock - (stepPaid + 1) := by omega
        change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1 - stepPaid} at stepFrame
        rw [clocks] at stepFrame
        exact stepFrame

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.general_chain_execute
