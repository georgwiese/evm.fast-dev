import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

namespace InitECandidate.Solver.Input.DeclarationCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Last declaration wins, exactly as in the real declaration evaluator. -/
def lastEntry {α β : Type} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | entry :: rest, key =>
      match lastEntry rest key with
      | some value => some value
      | none => if entry.1 == key then some entry.2 else none

theorem update_lookup {α β : Type} [BEq α]
    (mapping : α → Option β) (entries : List (α × β)) (key : α) :
    FUPDATE_LIST mapping entries key =
      match lastEntry entries key with
      | some value => some value
      | none => mapping key := by
  induction entries generalizing mapping with
  | nil => rfl
  | cons entry rest ih =>
      rw [FUPDATE_LIST_cons, ih]
      simp only [lastEntry]
      cases lastEntry rest key with
      | some value => rfl
      | none => simp only [FUPDATE]; split <;> rfl

/-- A successful real declaration pass installs its literal function bodies.
No successful function execution or initially empty code map is required. -/
theorem installed {width : Nat} {F : Type} [NeZero width]
    (source target : PanSemStateFiniteExact width F) [DecidablePred source.memaddrs]
    (program : List (DeclHOL width))
    (run : evaluateDeclsHOLFinite source program = some target)
    (name : MlS) (entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
    (found : lastEntry (functionsHOL program) name = some entry) :
    target.code.lookup name = some entry := by
  rw [evaluateDeclsHOLFinite_functions source program target run,
    HolFiniteMapExact.lookup_updateList, update_lookup, found]

theorem lastEntry_of_mem {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) (value : β)
    (member : (key, value) ∈ entries) (distinct : (entries.map Prod.fst).Nodup) :
    lastEntry entries key = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
      obtain ⟨head, payload⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with first | later
      · cases first
        have absent : lastEntry rest key = none := by
          clear ih
          induction rest with
          | nil => rfl
          | cons entry tail ih =>
              simp only [List.map_cons, List.mem_cons, not_or] at distinct
              rw [lastEntry, ih ⟨distinct.1.2, distinct.2.of_cons⟩ (by simp)]
              simp [Ne.symm distinct.1.1]
        simp [lastEntry, absent]
      · rw [lastEntry, ih later distinct.2]

end InitECandidate.Solver.Input.DeclarationCode

#print axioms InitECandidate.Solver.Input.DeclarationCode.installed
#print axioms InitECandidate.Solver.Input.DeclarationCode.lastEntry_of_mem
