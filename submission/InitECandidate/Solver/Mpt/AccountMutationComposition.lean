import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

variable {ι : Type} [Fintype ι]
variable {source middle post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {cursor middleCursor nextCursor cutoff protectedCursor base cap count middleCount nextCount : Nat}
variable {objects middleObjects next : ι → TableFamily.Object} {outer : ι}
variable {middleEntries nextEntries : Nat → Journal.Entry ι}
variable {accounts middleAccounts nextAccounts : List (BitVec 64)}
variable {property middleProperty nextProperty : ι → BitVec 64 → Prop}
variable {firstPrice secondPrice firstAppends secondAppends firstPopulation secondPopulation : Nat}

theorem Result.trans
    (first : Result source middle cursor middleCursor cutoff protectedCursor objects middleObjects outer base cap count middleCount middleEntries accounts middleAccounts property middleProperty firstPrice firstAppends firstPopulation)
    (second : Result middle post middleCursor nextCursor cutoff protectedCursor middleObjects next outer base cap middleCount nextCount nextEntries middleAccounts nextAccounts middleProperty nextProperty secondPrice secondAppends secondPopulation) :
    Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
      (firstPrice + secondPrice) (firstAppends + secondAppends) secondPopulation := by
  have clocks : source.clock - post.clock = (source.clock - middle.clock) + (middle.clock - post.clock) := by
    have := first.clockForward
    have := second.clockForward
    omega
  have counts : nextCount - count = (middleCount - count) + (nextCount - middleCount) := by
    have := first.countForward
    have := second.countForward
    omega
  refine {
    clockForward := Nat.le_trans second.clockForward first.clockForward
    cursorForward := Nat.le_trans first.cursorForward second.cursorForward
    protectedBefore := first.protectedBefore
    countForward := Nat.le_trans first.countForward second.countForward
    countBound := second.countBound
    appends := ?_
    family := second.family
    image := second.image
    zone := second.zone
    work := ?_
    populations := second.populations
    code := second.code.trans first.code
    oracle := second.oracle.trans first.oracle
    environment := second.environment
    globals := first.globals.trans second.globals
    values := second.values
    savedValues := second.savedValues
    registry := second.registry
    extension := first.extension.trans second.extension first.cursorForward
    effect := ?_
    metadata := first.metadata.trans second.metadata
    frame := ?_
    counter := second.counter
    propertyIncluded := fun index value owned => second.propertyIncluded index value (first.propertyIncluded index value owned)
    outerValues := fun value => (second.outerValues value).trans (first.outerValues value)
    readerKnown := ?_ }
  · rw [counts]
    exact Nat.add_le_add first.appends second.appends
  · have firstWork := first.work
    have secondWork := second.work
    rw [clocks]
    omega
  · rw [counts]
    simpa only [Nat.add_zero] using first.effect.trans second.effect
  · intro query above before outside away
    have one := first.frame query above before outside away
    have two := second.frame query above before one.1 away
    exact ⟨two.1,two.2.trans one.2⟩
  · intro index kind known
    exact second.readerKnown index ((first.metadata.kinds index).trans kind) (first.readerKnown index kind known)

theorem Result.locals
    (result : Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty firstPrice firstAppends firstPopulation)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    Result source {post with locals := locals} cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty firstPrice firstAppends firstPopulation := by
  let finish := {post with locals := locals}
  exact {
    clockForward := result.clockForward
    cursorForward := result.cursorForward
    protectedBefore := result.protectedBefore
    countForward := result.countForward
    countBound := result.countBound
    appends := result.appends
    family := result.family.of_control rfl rfl rfl rfl
    image := result.image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) result.image.separate
    zone := result.zone
    work := result.work
    populations := result.populations
    code := result.code
    oracle := result.oracle
    environment := result.environment.of_fields rfl rfl rfl
    globals := result.globals
    values := result.values
    savedValues := result.savedValues
    registry := result.registry.framed post finish cutoff nextCursor nextCursor next next nextAccounts (TableFamily.PersistentFrame.of_memory cutoff nextCursor next post finish rfl) (Nat.le_refl _) rfl
    extension := result.extension
    effect := result.effect
    metadata := result.metadata
    frame := result.frame
    counter := result.counter
    propertyIncluded := result.propertyIncluded
    outerValues := result.outerValues
    readerKnown := result.readerKnown }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.trans
#print axioms InitECandidate.Solver.Mpt.AccountMutation.Result.locals
