import InitECandidate.Solver.MutableTable.HasModelExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original membership return derives its binary answer, clock
price and complete nonlocal read-only frame without an entry allowance. -/
theorem model_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    ∃ paid flag, paid ≤ bodyPrice kind slots.length ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      returned = .val (.word flag) ∧ emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  let extra := bodyPrice kind slots.length
  let padded := {source with clock := source.clock + extra}
  have paddedTable : TableState padded kind plan slots cursor floor := table.of_fields rfl rfl rfl rfl
  obtain ⟨paid, flag, post, bounded, flagBound, actual, modelFrame⟩ :=
    model_execute padded kind plan slots cursor floor paddedTable (environment.of_fields rfl rfl rfl) query queryFits queryMapped tableLocal keyLocal (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) target extra
    ⟨normal, by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + extra} = post at postEq
  have frame : emptyLocalsHOLFinite {target with clock := target.clock + extra} =
      emptyLocalsHOLFinite {source with clock := source.clock + extra - paid} := by
    rw [postEq]
    exact modelFrame
  have stripped := InitECandidate.Solver.strip_clock_padding source target source paid extra (by change paid ≤ extra at bounded; omega) frame
  refine ⟨paid, flag, bounded, stripped.1, flagBound, ?_, stripped.2⟩
  simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.model_body_normal
