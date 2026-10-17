import InitECandidate.Solver.WitnessRadix.CountStep
import InitECandidate.Solver.WitnessRadix.CountPost
import InitECandidate.Solver.WitnessRadix.BuildCopyLoop

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def countLoop : ProgHOL 64 := .while BuildProgram.condition body
def zeroCount (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) : Nat :=
  (input.filter fun ordinal => !ByteKeys.bit (keyFor ordinal) position).length

/-- The literal counting loop counts precisely the zero-bit subsequence,
restores all temporary locals and consumes one clock per input ordinal. -/
theorem loop_execute {F : Type} (input : List (BitVec 64))
    (source : PanSemStateFiniteExact 64 F) (src start keys zeros : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position index count : Nat)
    (inside : position < 256) (small : count < 2 ^ 64) (size : index + input.length = count)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))))
    (rows : BuildCopy.Rows source.memory source.memaddrs src start index input)
    (views : ∀ ordinal ∈ input, MemoryBytes.ByteView source (keys + ordinal * 32#64) (keyFor ordinal))
    (enough : input.length ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source countLoop = (none, target) ∧
      target.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 count))) ∧
      target.locals.lookup (ofString "zeros") =
        some (.val (.word (zeros + BitVec.ofNat 64 (zeroCount keyFor position input)))) ∧
      (∀ name : MlS, ofString "i" ≠ name → ofString "zeros" ≠ name →
        target.locals.lookup name = source.locals.lookup name) ∧
      emptyLocalsHOLFinite target =
        emptyLocalsHOLFinite { source with clock := source.clock - input.length } := by
  classical
  induction input generalizing source index zeros with
  | nil =>
      have same : index = count := by simpa using size
      subst index
      refine ⟨source, ?_, indexLocal, ?_, ?_, ?_⟩
      · rw [countLoop, evaluateHOLFiniteState_while_total,
          BuildCopy.condition_read source count count small (by omega) indexLocal countLocal]
        simp
      · simpa [zeroCount] using zerosLocal
      · intros; rfl
      · simp
  | cons ordinal rest ih =>
      obtain ⟨mapped, stored, restRows⟩ := rows
      have active : index < count := by simp only [List.length_cons] at size; omega
      have nonzero : source.clock ≠ 0 := by simp only [List.length_cons] at enough; omega
      let entry := decClockHOLFinite source
      let digit := if ByteKeys.bit (keyFor ordinal) position then 1#64 else 0#64
      let next := counterPost entry digit zeros (BitVec.ofNat 64 index)
      let nextZeros := if ByteKeys.bit (keyFor ordinal) position then zeros else zeros + 1#64
      have view := views ordinal (by simp)
      have view' := MemoryBytes.byteView_of_fields source entry rfl rfl rfl _ _ view
      have bodyRun : evaluateHOLFiniteState entry body = (none, next) :=
        iteration entry src start (BitVec.ofNat 64 index) keys ordinal zeros position (keyFor ordinal)
          inside srcLocal startLocal indexLocal keysLocal bitLocal zerosLocal mapped stored view'
      have fields : emptyLocalsHOLFinite next = emptyLocalsHOLFinite entry :=
        counter_frame entry digit zeros (BitVec.ofNat 64 index)
      have memoryEq : next.memory = source.memory := congrArg (fun state => state.memory) fields
      have domainEq : next.memaddrs = source.memaddrs := congrArg (fun state => state.memaddrs) fields
      have endianEq : next.be = source.be := congrArg (fun state => state.be) fields
      have clockEq : next.clock = entry.clock := congrArg (fun state => state.clock) fields
      have src' : next.locals.lookup (ofString "src") = some (.val (.word src)) := by
        rw [counter_other entry digit zeros (BitVec.ofNat 64 index) "src" (by decide) (by decide)]
        exact srcLocal
      have start' : next.locals.lookup (ofString "start") = some (.val (.word start)) := by
        rw [counter_other entry digit zeros (BitVec.ofNat 64 index) "start" (by decide) (by decide)]
        exact startLocal
      have keys' : next.locals.lookup (ofString "keys") = some (.val (.word keys)) := by
        rw [counter_other entry digit zeros (BitVec.ofNat 64 index) "keys" (by decide) (by decide)]
        exact keysLocal
      have bit' : next.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))) := by
        rw [counter_other entry digit zeros (BitVec.ofNat 64 index) "bit" (by decide) (by decide)]
        exact bitLocal
      have count' : next.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))) := by
        rw [counter_other entry digit zeros (BitVec.ofNat 64 index) "count" (by decide) (by decide)]
        exact countLocal
      have index' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
        have eq := counter_index entry digit zeros (BitVec.ofNat 64 index)
        simpa only [← BitVec.ofNat_add] using eq
      have zeros' : next.locals.lookup (ofString "zeros") = some (.val (.word nextZeros)) := by
        have eq := counter_zeros entry digit zeros (BitVec.ofNat 64 index) zerosLocal
        cases bit : ByteKeys.bit (keyFor ordinal) position <;>
          simpa [next, digit, nextZeros, bit] using eq
      have rows' : BuildCopy.Rows next.memory next.memaddrs src start (index + 1) rest := by
        rw [memoryEq, domainEq]
        exact restRows
      have views' : ∀ value ∈ rest, MemoryBytes.ByteView next (keys + value * 32#64) (keyFor value) := by
        intro value member
        exact MemoryBytes.byteView_of_fields source next memoryEq.symm domainEq.symm endianEq.symm
          _ _ (views value (List.mem_cons_of_mem ordinal member))
      obtain ⟨target, run, finalIndex, finalZeros, finalOther, finalFrame⟩ := ih next nextZeros (index + 1)
        (by simp only [List.length_cons] at size; omega) src' start' keys' bit' zeros' index' count'
        rows' views' (by
          rw [clockEq]
          change rest.length ≤ source.clock - 1
          simp only [List.length_cons] at enough
          omega)
      refine ⟨target, ?_, finalIndex, ?_, ?_, ?_⟩
      · rw [countLoop, evaluateHOLFiniteState_while_total,
          BuildCopy.condition_read source index count small (by omega) indexLocal countLocal]
        simp only [if_pos active]
        rw [if_pos (by decide)]
        have bodyRun' : evaluateHOLFiniteState (decClockHOLFinite source) body = (none, next) := bodyRun
        simp only [if_neg nonzero, bodyRun']
        have fixed : fixClockHOLFinite entry ((none : Option (PanSemResultExact 64)), next) = (none, next) := by
          simp [fixClockHOLFinite, ← clockEq]
        change (let output := fixClockHOLFinite entry (none, next);
          evaluateHOLFiniteState output.2 countLoop) = _
        simpa only [fixed] using run
      · cases bit : ByteKeys.bit (keyFor ordinal) position <;>
          simpa [zeroCount, List.filter_cons, bit, nextZeros, BitVec.ofNat_add,
            BitVec.add_assoc, BitVec.add_comm] using finalZeros
      · intro name notI notZeros
        rw [finalOther name notI notZeros]
        exact counter_lookup entry digit zeros (BitVec.ofNat 64 index) name notI notZeros
      · rw [finalFrame]
        have shifted := congrArg (fun state : PanSemStateFiniteExact 64 F =>
          { state with clock := state.clock - rest.length }) fields
        have clockSub : source.clock - 1 - rest.length = source.clock - (ordinal :: rest).length := by
          simp only [List.length_cons]
          omega
        simpa only [emptyLocalsHOLFinite, entry, decClockHOLFinite, clockSub] using shifted

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.loop_execute
