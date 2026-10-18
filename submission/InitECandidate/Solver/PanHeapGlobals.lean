import InitECandidate.Solver.PanState

namespace InitECandidate.Solver
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Persistent allocation phases may update heap_ptr; every other global
retains its actual incoming binding, including arena and parent cursors. -/
def HeapGlobals {F : Type} (source target : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ key : MlS, key ≠ ofString "heap_ptr" → target.globals.lookup key = source.globals.lookup key

theorem HeapGlobals.refl {F : Type} (source : PanSemStateFiniteExact 64 F) : HeapGlobals source source := by
  intro key different
  rfl

theorem HeapGlobals.trans {F : Type} {source middle target : PanSemStateFiniteExact 64 F}
    (first : HeapGlobals source middle) (second : HeapGlobals middle target) : HeapGlobals source target := by
  intro key different
  exact (second key different).trans (first key different)

theorem HeapGlobals.update {F : Type} (source : PanSemStateFiniteExact 64 F) (word : BitVec 64) :
    HeapGlobals source {source with globals := source.globals.update (ofString "heap_ptr", .val (.word word))} := by
  intro key different
  simp [HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]

end InitECandidate.Solver

#print axioms InitECandidate.Solver.HeapGlobals.trans
#print axioms InitECandidate.Solver.HeapGlobals.update
