import InitECandidate.Solver.Mpt.CommonPrefixReturned
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_minimum_effects (code) : Input.LocalEffects.Preserves code afterMinimum := by
  unfold afterMinimum loopAndAfter loopBody guard advance
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.sequence
  · apply Input.LocalEffects.loop
    apply Input.LocalEffects.sequence
    · exact Input.LocalEffects.conditional code _ _ _ (Input.LocalEffects.returned code _) (Input.LocalEffects.skip code)
    · exact Input.LocalEffects.assign code _ _
  · exact Input.LocalEffects.returned code _

theorem after_minimum_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length≤64) (nCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterMinimum=(some (.returned value),target)) :
    ∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤length := by
  rw [afterMinimum] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "i" .one (.const 0#64) loopAndAfter value normal
  have valueEq : declared=.val (.word 0#64):=Option.some.inj read.symm
  subst declared
  let current:=bind source "i" 0#64
  have currentN : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans nCell
  have valid : Input.GuardedCounterLoop.Invariant length current:=⟨0#64,bind_lookup_same _ _ _,currentN,by change 0≤length; omega⟩
  exact loop_and_after_normal current inner length small valid value continued

/-- Original path comparison returns a word no larger than either input
path length and preserves all nonlocal state. Its actual cost and result
follow from execution without mapped-byte or entry-clock premises. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : BitVec 64)
    (small : min left.toNat right.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "al")=some (.val (.word left)))
    (rightCell : source.locals.lookup (ofString "bl")=some (.val (.word right)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ word : BitVec 64,value=.val (.word word) ∧ word.toNat≤min left.toNat right.toNat ∧
      source.clock-target.clock≤min left.toNat right.toNat+1 ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have cost:=body_cost source left right small installed leftCell rightCell
  rw [normal] at cost
  rw [body_shape] at normal
  have funded:=Input.CallNormal.normal_clock source target (ofString "n") .one (ofString "min") minimumArguments afterMinimum value normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) minimumArguments=
      some [.val (.word left),.val (.word right)]:=by
    simp [minimumArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,rightCell]
  have actual:=GasBudget.Minimum.call_execute source left right "n" minimumArguments afterMinimum args (minimum_code source.code installed) funded
  have joined:=actual.symm.trans normal
  let current:=bind {source with clock:=source.clock-1} "n" (GasBudget.Minimum.selected left right)
  let inner:=(evaluateHOLFiniteState current afterMinimum).2
  have resultEq:=congrArg Prod.fst joined
  have continued : evaluateHOLFiniteState current afterMinimum=(some (.returned value),inner):=
    Prod.ext resultEq rfl
  have endpoint : target=restore source "n" inner:=(congrArg Prod.snd joined).symm
  have selectedEq : GasBudget.Minimum.selected left right=BitVec.ofNat 64 (min left.toNat right.toNat):=by
    rw [←GasBudget.Minimum.selected_number left right]
    simp
  have currentN : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (min left.toNat right.toNat)))):=by
    rw [←selectedEq]
    exact bind_lookup_same _ _ _
  obtain ⟨word,answer,bound⟩:=after_minimum_normal current inner (min left.toNat right.toNat) small currentN value continued
  have frame:=after_minimum_effects source.code current rfl
  rw [continued] at frame
  refine ⟨word,answer,bound,cost,?_⟩
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.after_minimum_effects
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.after_minimum_normal
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.body_normal
