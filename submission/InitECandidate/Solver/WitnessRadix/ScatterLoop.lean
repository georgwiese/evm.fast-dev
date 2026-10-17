import InitECandidate.Solver.WitnessRadix.ScatterReady
import InitECandidate.Solver.WitnessRadix.ScatterStep
import InitECandidate.Solver.WitnessRadix.BuildCopyLoop

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def scatterLoop : ProgHOL 64 := .while BuildProgram.condition body
def keep (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (ordinal : BitVec 64) : Bool :=
  ByteKeys.bit (keyFor ordinal) position
def zeroAdvance (zero : Nat) (selected : Bool) : Nat := if selected then zero else zero + 1
def oneAdvance (one : Nat) (selected : Bool) : Nat := if selected then one + 1 else one
def zeros (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) : Nat :=
  (input.filter fun ordinal => !keep keyFor position ordinal).length
def ones (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) : Nat :=
  (input.filter (keep keyFor position)).length

def scatterState {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) :
    List (BitVec 64) → Nat → Nat → Nat → PanSemStateFiniteExact 64 F
  | [], _, _, _ => source
  | ordinal :: rest, index, zero, one =>
      scatterState (post (decClockHOLFinite source) dst (flagWord (keep keyFor position ordinal)) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)) dst keyFor position
        rest (index + 1) (zeroAdvance zero (keep keyFor position ordinal))
          (oneAdvance one (keep keyFor position ordinal))

/-- Complete literal stable-scatter loop, from mapped and separated writable
arrays and readable key bytes. The exact poststate includes every store. -/
theorem loop_execute {F : Type} (input : List (BitVec 64))
    (source : PanSemStateFiniteExact 64 F) (src dst start keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position index count zero one limit : Nat)
    (inside : position < 256) (small : count < 2 ^ 64) (size : index + input.length = count)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))))
    (zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word (BitVec.ofNat 64 zero))))
    (oneLocal : source.locals.lookup (ofString "one_cursor") = some (.val (.word (BitVec.ofNat 64 one))))
    (ready : Ready source src dst start keys keyFor input index limit)
    (zeroRoom : zero + zeros keyFor position input ≤ limit)
    (oneRoom : one + ones keyFor position input ≤ limit)
    (enough : input.length ≤ source.clock) :
    evaluateHOLFiniteState source scatterLoop =
      (none, scatterState source dst keyFor position input index zero one) := by
  classical
  induction input generalizing source index zero one with
  | nil =>
      have same : index = count := by simpa using size
      subst index
      rw [scatterLoop, evaluateHOLFiniteState_while_total,
        BuildCopy.condition_read source count count small (by omega) indexLocal countLocal]
      simp [scatterState]
  | cons ordinal rest ih =>
      let selected := keep keyFor position ordinal
      let entry := decClockHOLFinite source
      let next := post entry dst (flagWord selected) ordinal
        (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have active : index < count := by simp only [List.length_cons] at size; omega
      have nonzero : source.clock ≠ 0 := by simp only [List.length_cons] at enough; omega
      have room : (if selected then one else zero) < limit := by
        cases bit : keep keyFor position ordinal <;>
          simp [zeros, ones, List.filter_cons, bit] at zeroRoom oneRoom <;>
          simp only [selected, bit, Bool.false_eq_true, ↓reduceIte] <;> omega
      have readyEntry := ready_of_fields source entry rfl rfl rfl _ _ _ _ _ _ _ _ ready
      have destinationMapped : entry.memaddrs (dst +
          (if ByteKeys.bit (keyFor ordinal) position then BitVec.ofNat 64 one else BitVec.ofNat 64 zero) * 8#64) := by
        have mapped := readyEntry.mapped _ room
        cases bit : keep keyFor position ordinal <;>
          simp only [keep] at bit <;>
          simpa [wordAddress, selected, keep, bit] using mapped
      have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) body = (none, next) :=
        iteration entry src dst start (BitVec.ofNat 64 index) keys ordinal (BitVec.ofNat 64 zero)
          (BitVec.ofNat 64 one) position (keyFor ordinal) inside srcLocal dstLocal startLocal indexLocal
          keysLocal bitLocal zeroLocal oneLocal readyEntry.rows.1 readyEntry.rows.2.1
          (readyEntry.views ordinal (by simp)) destinationMapped
      have readyNext := ready_next entry src dst start keys ordinal keyFor rest index limit zero one selected readyEntry room
      have other (name : MlS) (notI : ofString "i" ≠ name) (notZero : ofString "zero_cursor" ≠ name)
          (notOne : ofString "one_cursor" ≠ name) : next.locals.lookup name = source.locals.lookup name :=
        post_lookup entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one)
          (BitVec.ofNat 64 index) name notI notZero notOne
      have index' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
        have eq := post_index entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
          (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
        simpa only [← BitVec.ofNat_add] using eq
      have zero' : next.locals.lookup (ofString "zero_cursor") =
          some (.val (.word (BitVec.ofNat 64 (zeroAdvance zero selected)))) := by
        have eq := post_zero entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
          (BitVec.ofNat 64 one) (BitVec.ofNat 64 index) zeroLocal
        cases bit : selected <;> simpa [next, flagWord, bit, zeroAdvance, BitVec.ofNat_add] using eq
      have one' : next.locals.lookup (ofString "one_cursor") =
          some (.val (.word (BitVec.ofNat 64 (oneAdvance one selected)))) := by
        have eq := post_one entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
          (BitVec.ofNat 64 one) (BitVec.ofNat 64 index) oneLocal
        cases bit : selected <;> simpa [next, flagWord, bit, oneAdvance, BitVec.ofNat_add] using eq
      have zeroRoom' : zeroAdvance zero selected + zeros keyFor position rest ≤ limit := by
        cases bit : keep keyFor position ordinal <;>
          simpa [zeros, List.filter_cons, selected, zeroAdvance, bit,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using zeroRoom
      have oneRoom' : oneAdvance one selected + ones keyFor position rest ≤ limit := by
        cases bit : keep keyFor position ordinal <;>
          simpa [ones, List.filter_cons, selected, oneAdvance, bit,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using oneRoom
      have fields := post_frame entry dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
        (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
      have clockEq : next.clock = entry.clock := congrArg (fun state => state.clock) fields
      have tailRun := ih next (index + 1) (zeroAdvance zero selected) (oneAdvance one selected)
        (by simp only [List.length_cons] at size; omega)
        ((other _ (by decide) (by decide) (by decide)).trans srcLocal)
        ((other _ (by decide) (by decide) (by decide)).trans dstLocal)
        ((other _ (by decide) (by decide) (by decide)).trans startLocal)
        ((other _ (by decide) (by decide) (by decide)).trans keysLocal)
        ((other _ (by decide) (by decide) (by decide)).trans bitLocal) index'
        ((other _ (by decide) (by decide) (by decide)).trans countLocal)
        zero' one' readyNext zeroRoom' oneRoom' (by
          rw [clockEq]
          change rest.length ≤ source.clock - 1
          simp only [List.length_cons] at enough
          omega)
      rw [scatterLoop, evaluateHOLFiniteState_while_total,
        BuildCopy.condition_read source index count small (by omega) indexLocal countLocal]
      simp only [if_pos active]
      rw [if_pos (by decide)]
      simp only [if_neg nonzero, bodyRun]
      have fixed : fixClockHOLFinite entry ((none : Option (PanSemResultExact 64)), next) = (none, next) := by
        simp [fixClockHOLFinite, ← clockEq]
      change (let output := fixClockHOLFinite entry (none, next);
        evaluateHOLFiniteState output.2 scatterLoop) = _
      simpa only [fixed, scatterState] using tailRun

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.loop_execute
