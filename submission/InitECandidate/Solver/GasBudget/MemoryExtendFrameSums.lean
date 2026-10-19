import InitECandidate.Solver.GasBudget.MemoryExtendCall
import InitECandidate.Solver.GasBudget.FrameRank

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem call_sums (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat) (arguments : List (ExpHOL 64))
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (argsRead : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word expand)])
    (ancestors : List (BitVec 64))
    (owned : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      Arenas.Outside base scratch (ancestor + BitVec.ofNat 64 offset))
    (apart : ∀ ancestor ∈ ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      ancestor + BitVec.ofNat 64 offset ≠ frame + 32#64 ∧ ancestor + BitVec.ofNat 64 offset ≠ frame + 40#64)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "extend_memory") arguments) = (none, post)) :
    price length capacity expand + 1 ≤ source.clock ∧
      post.clock = source.clock - (price length capacity expand + 1) ∧
      View post frame base (newLength length expand) (nextCapacity length capacity expand) (base + nextCapacity length capacity expand) scratch ∧
      FrameSums.budget post.memory (frame :: ancestors) = FrameSums.budget source.memory (frame :: ancestors) ∧
      FrameSums.used post.memory (frame :: ancestors) = FrameSums.used source.memory (frame :: ancestors) := by
  obtain ⟨funded, clock, postView, locals, away⟩ := call_normal source post frame base length capacity pointer scratch expand amount used arguments view advance argsRead normal
  have header : ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (frame + BitVec.ofNat 64 offset) = source.memory (frame + BitVec.ofNat 64 offset) := by
    intro offset member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact away _ (view.header_outside _ (by decide)) (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))
  have cells : ∀ current ∈ frame :: ancestors, ∀ offset ∈ ([64, 184, 192] : List Nat),
      post.memory (current + BitVec.ofNat 64 offset) = source.memory (current + BitVec.ofNat 64 offset) := by
    intro current member offset inside
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact header offset inside
    · obtain ⟨notLength, notCapacity⟩ := apart current member offset inside
      exact away _ (owned current member offset inside) notLength notCapacity
  exact ⟨funded, clock, postView, FrameSums.budget_congr source.memory post.memory (frame :: ancestors) cells,
    FrameSums.used_congr source.memory post.memory (frame :: ancestors) (by intro current member; exact cells current member 184 (by simp))⟩

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.call_sums
