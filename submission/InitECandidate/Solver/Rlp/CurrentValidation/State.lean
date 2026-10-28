import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.Rlp.ValidationBodyCost
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- An actual continuing parse has never entered a nested scratch frame.
The cursor/domain facts are the current initialized ones, not mapped scratch. -/
structure State (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending go : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position))
  endCell : source.locals.lookup (ofString "end")=some (.val (.word ending))
  topCell : source.locals.lookup (ofString "top")=some (.val (.word 0#64))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word go))
  ordered : position.toNat≤ending.toNat
  binary : go=0#64 ∨ go=1#64
  inactive : go=0#64 → position=ending

variable {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {position ending go : BitVec 64}

theorem State.at_clock (data : State source position ending go) (clock : Nat) :
    State {source with clock:=clock} position ending go :=
  ⟨data.arena.of_frame rfl,data.positionCell,data.endCell,data.topCell,data.goCell,data.ordered,data.binary,data.inactive⟩

theorem State.bound_value (data : State source position ending go) (name : String) (value : ValueHOL 64)
    (different : ofString name≠ofString "pos" ∧ ofString name≠ofString "end" ∧ ofString name≠ofString "top" ∧ ofString name≠ofString "go") :
    State (setVarHOLFinite (ofString name) value source) position ending go := by
  have cell (key : String) (other : ofString name≠ofString key) :
      (setVarHOLFinite (ofString name) value source).locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  exact ⟨data.arena.of_frame rfl,(cell "pos" different.1).trans data.positionCell,(cell "end" different.2.1).trans data.endCell,
    (cell "top" different.2.2.1).trans data.topCell,(cell "go" different.2.2.2).trans data.goCell,data.ordered,data.binary,data.inactive⟩

theorem State.restored (data : State post position ending go) (saved : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (different : ofString name≠ofString "pos" ∧ ofString name≠ofString "end" ∧ ofString name≠ofString "top" ∧ ofString name≠ofString "go") :
    State (restore saved name post) position ending go :=
  ⟨data.arena.of_frame rfl,(restore_lookup_other saved post name "pos" (Ne.symm different.1)).trans data.positionCell,
    (restore_lookup_other saved post name "end" (Ne.symm different.2.1)).trans data.endCell,
    (restore_lookup_other saved post name "top" (Ne.symm different.2.2.1)).trans data.topCell,
    (restore_lookup_other saved post name "go" (Ne.symm different.2.2.2)).trans data.goCell,data.ordered,data.binary,data.inactive⟩

theorem State.moved (data : State source position ending 1#64) (next : BitVec 64) (before : next.toNat≤ending.toNat) :
    State (bind source "pos" next) next ending 1#64 :=
  ⟨data.arena.of_frame rfl,bind_lookup_same source "pos" next,
    (bind_lookup_other source "pos" "end" next (by decide)).trans data.endCell,
    (bind_lookup_other source "pos" "top" next (by decide)).trans data.topCell,
    (bind_lookup_other source "pos" "go" next (by decide)).trans data.goCell,before,Or.inr rfl,by intro impossible; exact False.elim ((by decide : (1#64 : BitVec 64)≠0#64) impossible)⟩

theorem State.stopped (data : State source ending ending 1#64) : State (bind source "go" 0#64) ending ending 0#64 :=
  ⟨data.arena.of_frame rfl,(bind_lookup_other source "go" "pos" 0#64 (by decide)).trans data.positionCell,
    (bind_lookup_other source "go" "end" 0#64 (by decide)).trans data.endCell,
    (bind_lookup_other source "go" "top" 0#64 (by decide)).trans data.topCell,bind_lookup_same source "go" 0#64,
    Nat.le_refl _,Or.inl rfl,by intro _; rfl⟩

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.State.bound_value
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.State.restored
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.State.moved
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.State.stopped
