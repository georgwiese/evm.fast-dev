import InitECandidate.Solver.MutableTable.TableFamily

namespace InitECandidate.Solver.MutableTable.TableFamily

/-- The schema, allocation lifetime floor and actual header pointer remain
fixed through mutations, although pools/capacities/populations can change. -/
structure Metadata {ι : Type} (objects next : ι → Object) : Prop where
  kinds : ∀ index,(next index).kind=(objects index).kind
  floors : ∀ index,(next index).floor=(objects index).floor
  pointers : ∀ index,(next index).pointer=(objects index).pointer

theorem Metadata.refl {ι : Type} (objects : ι → Object) : Metadata objects objects :=
  ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl⟩

theorem Metadata.trans {ι : Type} {objects middle next : ι → Object}
    (first : Metadata objects middle) (second : Metadata middle next) : Metadata objects next :=
  ⟨fun index=>(second.kinds index).trans (first.kinds index),
    fun index=>(second.floors index).trans (first.floors index),
    fun index=>(second.pointers index).trans (first.pointers index)⟩

theorem Metadata.of_update {ι : Type} [DecidableEq ι] (objects : ι → Object) (writer : ι) (next : Object)
    (kind : next.kind=(objects writer).kind) (floor : next.floor=(objects writer).floor)
    (pointers : ∀ index,(Function.update objects writer next index).pointer=(objects index).pointer) :
    Metadata objects (Function.update objects writer next) := by
  refine ⟨?_,?_,pointers⟩
  · intro index
    by_cases same : index=writer
    · subst index; simpa only [Function.update_self] using kind
    · rw [Function.update_of_ne same]
  · intro index
    by_cases same : index=writer
    · subst index; simpa only [Function.update_self] using floor
    · rw [Function.update_of_ne same]

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.Metadata.refl
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Metadata.trans
#print axioms InitECandidate.Solver.MutableTable.TableFamily.Metadata.of_update
