import InitECandidate.Solver.Input.VarList.Unroll
import InitECandidate.Solver.Input.ScopeLookup
import InitECandidate.Solver.WitnessRadix.LoopCompose

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact symbolic store/update/scoping state for successive real iterations. -/
def walk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) : Nat→PanSemStateFiniteExact 64 Guest.HostMemory
  | 0=>source
  | rounds+1=>walk (iteration (decClockHOLFinite source) input plan index previous) input plan (index+1) (currentWord input plan.start index) rounds

theorem iteration_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) : (iteration source input plan index previous).clock=source.clock := rfl

theorem iteration_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) : WitnessRadix.BackingLayout.control (iteration source input plan index previous)=WitnessRadix.BackingLayout.control source := rfl

theorem iteration_index (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) :
    (iteration source input plan index previous).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
  rw [iteration,ScalarScope.restore_other source _ "o" "i" (by decide)]
  exact bind_lookup_same _ _ _

theorem iteration_previous (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) :
    (iteration source input plan index previous).locals.lookup (ofString "prev")=some (.val (.word (currentWord input plan.start index))) := by
  rw [iteration,ScalarScope.restore_other source _ "o" "prev" (by decide)]
  exact (bind_lookup_other _ "i" "prev" _ (by decide)).trans (bind_lookup_same _ _ _)

theorem iteration_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) (name : String)
    (i : ofString "i"≠ofString name) (p : ofString "prev"≠ofString name) (o : ofString "o"≠ofString name) :
    (iteration source input plan index previous).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [iteration,ScalarScope.restore_other source _ "o" name o]
  change (bind (bind (pointerState (bind source "o" (currentWord input plan.start index)) input plan index (currentWord input plan.start index) previous)
    "prev" (currentWord input plan.start index)) "i" (BitVec.ofNat 64 (index+1))).locals.lookup (ofString name)=_
  rw [bind_lookup_other _ "i" name _ i,bind_lookup_other _ "prev" name _ p]
  change (bind source "o" (currentWord input plan.start index)).locals.lookup (ofString name)=_
  exact bind_lookup_other source "o" name _ o

theorem walk_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) (rounds : Nat) :
    (walk source input plan index previous rounds).clock=source.clock-rounds := by
  induction rounds generalizing source index previous with
  | zero=>rfl
  | succ rounds ih=>
    rw [walk,ih,iteration_clock]
    change source.clock-1-rounds=source.clock-(rounds+1)
    omega

theorem walk_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) (rounds : Nat) :
    WitnessRadix.BackingLayout.control (walk source input plan index previous rounds)=WitnessRadix.BackingLayout.control source := by
  induction rounds generalizing source index previous with
  | zero=>rfl
  | succ rounds ih=>
    rw [walk,ih,iteration_control]
    rfl

theorem walk_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (previous : BitVec 64) (rounds : Nat) (name : String)
    (i : ofString "i"≠ofString name) (p : ofString "prev"≠ofString name) (o : ofString "o"≠ofString name) :
    (walk source input plan index previous rounds).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  induction rounds generalizing source index previous with
  | zero=>rfl
  | succ rounds ih=>
    rw [walk,ih,iteration_other _ _ _ _ _ name i p o]
    rfl

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.iteration_clock
#print axioms InitECandidate.Solver.Input.VarList.iteration_control
#print axioms InitECandidate.Solver.Input.VarList.iteration_index
#print axioms InitECandidate.Solver.Input.VarList.iteration_previous
#print axioms InitECandidate.Solver.Input.VarList.iteration_other
#print axioms InitECandidate.Solver.Input.VarList.walk_clock
#print axioms InitECandidate.Solver.Input.VarList.walk_control
#print axioms InitECandidate.Solver.Input.VarList.walk_other
