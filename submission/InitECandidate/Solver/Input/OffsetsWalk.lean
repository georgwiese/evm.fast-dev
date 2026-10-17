import InitECandidate.Solver.Input.OffsetsValidLoop

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem walk_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (index rounds : Nat) :
    emptyLocalsHOLFinite (walk source index rounds)=emptyLocalsHOLFinite {source with clock:=source.clock-rounds} := by
  induction rounds generalizing source index with
  | zero=>rfl
  | succ rounds ih=>
    rw [walk,ih]
    have clock : source.clock-1-rounds=source.clock-(rounds+1) := by omega
    change emptyLocalsHOLFinite {source with clock:=source.clock-1-rounds}=_
    rw [clock]

theorem walk_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (index rounds : Nat) :
    (walk source index rounds).clock=source.clock-rounds :=
  congrArg (fun state : PanSemStateFiniteExact 64 F=>state.clock) (walk_frame source index rounds)

theorem walk_other {F : Type} (source : PanSemStateFiniteExact 64 F) (index rounds : Nat) (name : MlS)
    (different : ofString "i"≠name) :
    (walk source index rounds).locals.lookup name=source.locals.lookup name := by
  induction rounds generalizing source index with
  | zero=>rfl
  | succ rounds ih=>
    rw [walk,ih]
    simp [WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    rfl

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.walk_frame
#print axioms InitECandidate.Solver.Input.Offsets.walk_clock
#print axioms InitECandidate.Solver.Input.Offsets.walk_other
