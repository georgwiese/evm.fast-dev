import InitECandidate.Solver.Input.ReturnNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.PureNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Recover a fixed pure value/clock contract from a real successful run.
Temporary padding supplies the executor's funding and is then removed. -/
theorem from_funded {F : Type} (source post : PanSemStateFiniteExact 64 F) (body : ProgHOL 64) (price : Nat)
    (expected actual : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned actual), post))
    (funded : ∀ entry : PanSemStateFiniteExact 64 F, entry.locals = source.locals → entry.code = source.code → price ≤ entry.clock →
      ∃ target, evaluateHOLFiniteState entry body = (some (.returned expected), target) ∧
        emptyLocalsHOLFinite target = emptyLocalsHOLFinite {entry with clock := entry.clock - price}) :
    actual = expected ∧ price ≤ source.clock ∧ post.clock = source.clock - price ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - price} := by
  have shifted := panPropsEvaluateAddClockEq body source (some (.returned actual)) post price
    ⟨normal, by intro impossible; cases impossible⟩
  obtain ⟨target, run, frame⟩ := funded {source with clock := source.clock + price} rfl rfl (by change price ≤ source.clock + price; omega)
  have resultEq := congrArg Prod.fst (shifted.symm.trans run)
  have valueEq : actual = expected := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  have stateEq := congrArg Prod.snd (shifted.symm.trans run)
  change {post with clock := post.clock + price} = target at stateEq
  rw [← stateEq] at frame
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change post.clock + price = source.clock + price - price at clock
  have fields := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with clock := state.clock - price}) frame
  have exactFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - price} := by
    simpa only [emptyLocalsHOLFinite, Nat.add_sub_cancel] using fields
  exact ⟨valueEq, by omega, by omega, exactFrame⟩

end InitECandidate.Solver.Input.PureNormal

#print axioms InitECandidate.Solver.Input.PureNormal.from_funded
