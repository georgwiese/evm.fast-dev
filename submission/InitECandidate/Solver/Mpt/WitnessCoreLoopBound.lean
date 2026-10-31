import InitECandidate.Solver.Mpt.WitnessCoreLoopCost
import InitECandidate.Solver.Input.ClockCostPotentialLoop

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

def Ranked (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rank : Nat) : Prop:=
  ∃ configuration : Configuration,Invariant databaseData frontier db limit source configuration ∧ configuration.rank limit=rank

def Valid (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=∃ rank,Ranked databaseData frontier db limit source rank

/-- The least rank among actual physical invariant descriptions of this
state. A normal next-state witness bounds its least rank from above; no
uniqueness assumption about descriptions or input hashes is required. -/
noncomputable def potential (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=by
  classical
  exact if valid : Valid databaseData frontier db limit source then Nat.find valid else 0

theorem potential_spec (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : Valid databaseData frontier db limit source) :
    Ranked databaseData frontier db limit source (potential databaseData frontier db limit source) := by
  classical
  rw [potential,dif_pos valid]
  exact Nat.find_spec valid

theorem potential_le (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant databaseData frontier db limit source configuration) :
    potential databaseData frontier db limit source≤configuration.rank limit := by
  classical
  have valid : Valid databaseData frontier db limit source:=⟨configuration.rank limit,configuration,invariant,rfl⟩
  rw [potential,dif_pos valid]
  exact Nat.find_min' valid ⟨configuration,invariant,rfl⟩

/-- All outcomes of the whole unchanged original238 while loop fit its
physical rank times the checked largest body price plus the real while
tick. Every continuing iteration derives its own smaller actual rank;
aborted iterations fit the same remaining allowance. -/
theorem Invariant.loop_cost (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant databaseData frontier db limit source configuration) :
    source.clock-(evaluateHOLFiniteState source (.while WitnessCore.condition loopBody)).2.clock≤
      (iterationCost+1)*configuration.rank limit := by
  classical
  let price:=iterationCost+1
  let allowance:=fun current=>price*potential databaseData frontier db limit current
  have step (current : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : current.code=source.code)
      (valid : Valid databaseData frontier db limit current) (word : BitVec 64)
      (guard : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) WitnessCore.condition=some (.val (.word word)))
      (nonzero : word≠0) (funded : current.clock≠0) :
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
      current.clock-output.2.clock≤allowance current ∧
      ((output.1=none ∨ output.1=some .continue)→ Valid databaseData frontier db limit output.2 ∧
        current.clock-output.2.clock+allowance output.2≤allowance current) := by
    obtain ⟨actual,ready,rankEq⟩:=potential_spec databaseData frontier db limit current valid
    have read:=ready.condition databaseData frontier db limit current actual
    have same : goWord actual.running=word:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans guard)))
    have running : actual.running=true:=by
      cases observed : actual.running with
      | false=>
        apply False.elim
        apply nonzero
        rw [←same,observed]
        rfl
      | true=>rfl
    have positive : 0<actual.rank limit:=by
      simp only [Configuration.rank,WitnessStackRank.rank,running,↓reduceIte]
      omega
    have atLeast : 1≤potential databaseData frontier db limit current:=by omega
    have budget : price≤allowance current:=by
      change price≤price*potential databaseData frontier db limit current
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left price atLeast
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) loopBody
    have nextReady:=ready.dec_clock databaseData frontier db limit current actual
    have bodyPaid:=nextReady.body_cost databaseData frontier db limit (decClockHOLFinite current) actual
    change current.clock-1-output.2.clock≤iterationCost at bodyPaid
    have paid : current.clock-output.2.clock≤price:=by unfold price; omega
    refine ⟨paid.trans budget,?_⟩
    intro continuing
    have noContinue:=loop_body_no_continue (decClockHOLFinite current)
    have normal : output.1=none:=continuing.resolve_right noContinue
    have run : evaluateHOLFiniteState (decClockHOLFinite current) loopBody=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,nextInvariant,smaller⟩:=nextReady.body_normal databaseData frontier db limit (decClockHOLFinite current) output.2 actual running run
    have nextValid : Valid databaseData frontier db limit output.2:=⟨next.rank limit,next,nextInvariant,rfl⟩
    have least:=potential_le databaseData frontier db limit output.2 next nextInvariant
    have shrink : potential databaseData frontier db limit output.2+1≤potential databaseData frontier db limit current:=by omega
    refine ⟨nextValid,?_⟩
    change current.clock-output.2.clock+price*potential databaseData frontier db limit output.2≤price*potential databaseData frontier db limit current
    calc
      current.clock-output.2.clock+price*potential databaseData frontier db limit output.2≤price+price*potential databaseData frontier db limit output.2:=Nat.add_le_add_right paid _
      _=price*(potential databaseData frontier db limit output.2+1):=by rw [Nat.mul_add,Nat.mul_one]; omega
      _≤price*potential databaseData frontier db limit current:=Nat.mul_le_mul_left price shrink
  have valid : Valid databaseData frontier db limit source:=⟨configuration.rank limit,configuration,invariant,rfl⟩
  have bounded:=Input.ClockCost.potential_loop source.code WitnessCore.condition loopBody (Valid databaseData frontier db limit) allowance step source rfl valid
  exact bounded.trans (Nat.mul_le_mul_left price (potential_le databaseData frontier db limit source configuration invariant))

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.potential_spec
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.potential_le
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.loop_cost
