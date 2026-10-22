import InitECandidate.Solver.Mpt.StateInitBlockFieldFrame

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

def fields (start : Nat) : List Action → List (Nat × BitVec 64)
  | []=>[]
  | action::rest=>(action.offset,action.value start)::fields (stepCursor start action) rest

theorem fields_offsets (start : Nat) (specs : List Action) :
    (fields start specs).map Prod.fst=specs.map Action.offset:=by
  induction specs generalizing start with
  | nil=>rfl
  | cons action rest ih=>simp only [fields,List.map_cons,ih]

/-- Every initialized block word is its last real stored value, including
the two ancestor-list zeros as well as all constructor pointers. -/
theorem fields_values (specs : List Action) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (wellFormed : ∀ action∈specs,action.Valid) (distinct : (specs.map Action.offset).Nodup)
    (layouts : Layouts start specs) (before : block+80≤start) :
    ∀ site∈fields start specs,(walk source block start specs).memory (MemoryRegion.address ⟨block,80⟩ site.1)=.word site.2:=by
  induction specs generalizing source start with
  | nil=>intro site impossible; cases impossible
  | cons action rest ih=>
    have noRepeat:=List.nodup_cons.mp distinct
    have tailValid : ∀ later∈rest,later.Valid:=fun later member=>wellFormed later (List.mem_cons_of_mem _ member)
    intro site member
    rcases List.mem_cons.mp member with equal|member
    · subst site
      exact field_after_walk rest source block start action recordValid (wellFormed action List.mem_cons_self) tailValid layouts.2 before
        (fun later member equal=>noRepeat.1 (List.mem_map.mpr ⟨later,member,equal.symm⟩))
    · exact ih (stepState source block start action) (stepCursor start action) tailValid noRepeat.2 layouts.2
        (before.trans (step_grows start action)) site member

theorem ancestor_sites (start : Nat) : (56,0#64)∈fields start actions ∧ (64,0#64)∈fields start actions:=by
  simp [fields,actions,Action.offset,Action.value]

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.fields_offsets
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.fields_values
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.ancestor_sites
