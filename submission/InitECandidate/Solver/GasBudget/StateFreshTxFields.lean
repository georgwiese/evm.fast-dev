import InitECandidate.Solver.GasBudget.StateFreshTxWordFrame

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def Fields {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tx : Nat)
    (objects : ι → TableFamily.Object) (specs : List Spec) : Prop :=
  ∀ spec ∈ specs, ∃ index, (objects index).kind = spec.kind ∧ (objects index).plan.capacity = spec.capacity ∧
    (objects index).slots = [] ∧ source.memory (MemoryRegion.address ⟨tx, 72⟩ spec.offset) = .word (objects index).pointer

theorem new_pointer (kind : KeyHash.Kind) (start capacity : Nat) :
    (Journal.newObject kind start capacity).pointer = BitVec.ofNat 64 start := by
  simp [TableFamily.Object.pointer, Journal.newObject, cell, fresh]

/-- Every original transaction-state field holds the pointer to its actual
new empty table; later constructors and distinct record stores preserve it. -/
theorem walk_fields {ι : Type} (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start tx : Nat) (objects : ι → TableFamily.Object)
    (recordValid : MemoryRegion.Valid ⟨tx, 72⟩) (afterRecord : tx + 72 ≤ start)
    (lower : 2701131776 ≤ start) (aligned : start % 8 = 0)
    (wellFormed : ∀ spec ∈ specs, spec.Valid) (distinct : (specs.map Spec.offset).Nodup)
    (room : cursor start specs ≤ 33806089496) :
    Fields (walk source start tx specs) tx (objectsAfter objects start specs) specs := by
  induction specs generalizing ι source start with
  | nil => intro spec member; cases member
  | cons spec specs ih =>
    have validSpec := wellFormed spec (by simp)
    have offsetBound := validSpec.2.2.2.1
    have nextRoom : freshEnd spec.kind start spec.capacity ≤ 33806089496 :=
      Nat.le_trans (cursor_forward specs (freshEnd spec.kind start spec.capacity)) room
    have valid := fresh_valid spec.kind start spec.capacity (Nat.two_pow_pos _) lower nextRoom aligned
    have nextAligned : freshEnd spec.kind start spec.capacity % 8 = 0 := by
      have position := valid.aligned .position
      change ((fresh spec.kind start spec.capacity).base .position + 8 * spec.capacity) % 8 = 0
      rw [Nat.add_mod, position]
      omega
    have forward : start ≤ freshEnd spec.kind start spec.capacity := by dsimp only [freshEnd]; omega
    have distinctParts := List.nodup_cons.mp distinct
    let newObjects := TableFamily.extend objects (Journal.newObject spec.kind start spec.capacity)
    have tailFields := ih (source := stepState source start tx spec) (start := freshEnd spec.kind start spec.capacity) newObjects
      (by omega) (by omega) nextAligned (by intro next member; exact wellFormed next (by simp [member])) distinctParts.2 room
    intro current member
    rcases List.mem_cons.mp member with same | member
    · subst current
      have chosen : objectsAfter objects start (spec :: specs) (embed specs.length (none : Option ι)) = Journal.newObject spec.kind start spec.capacity :=
        objectsAfter_old specs newObjects (freshEnd spec.kind start spec.capacity) none
      refine ⟨embed specs.length (none : Option ι), ?_⟩
      rw [chosen]
      refine ⟨rfl, rfl, rfl, ?_⟩
      rw [new_pointer]
      have before : (MemoryRegion.address ⟨tx, 72⟩ spec.offset).toNat < freshEnd spec.kind start spec.capacity := by
        rw [MemoryRegion.address_number ⟨tx, 72⟩ recordValid spec.offset (by change spec.offset ≤ 72; omega)]
        dsimp only [freshEnd]
        omega
      have kept := walk_word specs (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) tx
        (by omega) nextAligned (by intro next member; exact wellFormed next (by simp [member])) room _ before (by
          intro next member
          apply record_word_distinct tx recordValid spec.offset next.offset (by omega)
            (by have := (wellFormed next (by simp [member])).2.2.2.1; omega)
          intro same
          exact distinctParts.1 (List.mem_map.mpr ⟨next, member, same.symm⟩))
      exact kept.trans (by simp [stepState, StoreWord.put])
    · exact tailFields current member

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.new_pointer
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_fields
