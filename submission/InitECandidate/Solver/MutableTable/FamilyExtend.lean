import InitECandidate.Solver.MutableTable.TableFamily

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def extend {ι : Type} (objects : ι → Object) (fresh : Object) : Option ι → Object
  | none => fresh
  | some index => objects index

/-- Add one actual fresh table identity. The old physical pools precede the
new table's lifetime floor; all current models share the advanced cursor. -/
theorem Model.extend {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor : Nat} {objects : ι → Object}
    (family : Model source cursor objects) (fresh : Object)
    (table : TableState source fresh.kind fresh.plan fresh.slots cursor fresh.floor)
    (earlier : ∀ index pool, (objects index).plan.base pool + size (objects index).kind (objects index).plan pool ≤ fresh.floor) :
    Model source cursor (extend objects fresh) := by
  constructor
  · intro index
    cases index with
    | none => exact table
    | some index => exact family.tables index
  · intro first second different
    cases first with
    | none =>
      cases second with
      | none => exact (different rfl).elim
      | some second =>
        intro left right
        right
        have before := earlier second right
        have after := table.lower left
        exact Nat.le_trans before after
    | some first =>
      cases second with
      | none =>
        intro left right
        left
        exact Nat.le_trans (earlier first left) (table.lower right)
      | some second => exact family.apart first second (fun same => different (congrArg Option.some same))

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Model.extend
