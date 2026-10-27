import InitECandidate.Solver.Input.CurrentStartup.RequestCut
import InitECandidate.Solver.Input.RequestLoad

namespace InitECandidate.Solver.Input.CurrentStartup.RequestPositions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem declared_exact {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (expression : ExpHOL 64) (value : ValueHOL 64)
    (read : eval source expression = some value)
    (actual : CallPrefix.Reaches source (.declare name .one expression) target) :
    target = setVarHOLFinite name value source := by
  cases actual with
  | declare _ _ _ observed actualRead checked =>
    have same := Option.some.inj (actualRead.symm.trans read)
    subst observed
    rfl

/-- The real setup declarations derive np and nlen from the validated outer
workspace cells. The intervening allocation and chain-ID store retain the
caller locals; no successful future declaration is assumed. -/
theorem bindings {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (pointer array : BitVec 64) (witness : Nat) (witnessLower : 16 ≤ witness)
    (pCell : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (firstMapped : source.memaddrs array) (secondMapped : source.memaddrs (array + 8#64))
    (firstCell : source.memory array = .word 16#64)
    (secondCell : source.memory (array + 8#64) = .word (BitVec.ofNat 64 witness))
    (actual : CallPrefix.Execution source RequestCut.actions target) :
    target.locals.lookup (ofString "np") = some (.val (.word (pointer + 18#64))) ∧
    target.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 (witness - 16)))) := by
  have firstRead := Request.first_read source array offsets firstMapped firstCell
  have secondRead := Request.second_read source array witness offsets secondMapped secondCell
  cases actual with
  | @step _ firstState _ _ _ first rest =>
    have firstEq := declared_exact (ofString "o_npr") _ (.val (.word 16#64)) firstRead first
    subst firstState
    cases rest with
    | @step _ loadedState _ _ _ second rest =>
      have secondEq := declared_exact (ofString "o_wit") _ (.val (.word (BitVec.ofNat 64 witness))) secondRead second
      subst loadedState
      cases rest with
      | @step _ allocatedState _ _ _ allocated rest =>
        cases rest with
        | @step _ chainedState _ _ _ chain remainder =>
          have short := CallPrefix.Execution.step allocated (.step chain (.done chainedState))
          have kept (key : MlS) (other : key ≠ ofString "si") : chainedState.locals.lookup key =
              (setVarHOLFinite (ofString "o_wit") (.val (.word (BitVec.ofNat 64 witness)))
                (setVarHOLFinite (ofString "o_npr") (.val (.word 16#64)) source)).locals.lookup key :=
            short.keeps key (by
              intro action member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl
              · simpa [CallPrefix.Action.keeps] using Ne.symm other
              · rfl)
          have p : chainedState.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))) := by
            rw [kept (ofString "p") (by decide)]
            simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
              show ofString "o_npr" ≠ ofString "p" from by decide,
              show ofString "o_wit" ≠ ofString "p" from by decide] using pCell
          have npr : chainedState.locals.lookup (ofString "o_npr") = some (.val (.word 16#64)) := by
            rw [kept (ofString "o_npr") (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "o_wit" ≠ ofString "o_npr" from by decide]
          have wit : chainedState.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 witness))) := by
            rw [kept (ofString "o_wit") (by decide)]
            simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
          have npRead : eval chainedState Request.pointerExpression = some (.val (.word (pointer + 18#64))) := by
            simp [eval, Request.pointerExpression, localVar, evalHOLExact, evalListHOLExact, toExact, p, npr,
              valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_assoc]
          cases remainder with
          | @step _ positionedState _ _ _ np last =>
            have npEq := declared_exact (ofString "np") _ (.val (.word (pointer + 18#64))) npRead np
            subst positionedState
            have subtract : BitVec.ofNat 64 witness - 16#64 = BitVec.ofNat 64 (witness - 16) :=
              BitVec.ofNat_sub_ofNat_of_le witness 16 (by decide) witnessLower
            have nlenRead : eval (setVarHOLFinite (ofString "np") (.val (.word (pointer + 18#64))) chainedState) Request.lengthExpression =
                some (.val (.word (BitVec.ofNat 64 (witness - 16)))) := by
              simp [eval, Request.lengthExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
                setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                show ofString "np" ≠ ofString "o_npr" from by decide,
                show ofString "np" ≠ ofString "o_wit" from by decide,
                npr, wit, valueIsWord, valueWord, wordOpHOL, wordOp, subtract]
            cases last with
            | @step _ finalState _ _ _ nlen done =>
              cases done
              have nlenEq := declared_exact (ofString "nlen") _ (.val (.word (BitVec.ofNat 64 (witness - 16)))) nlenRead nlen
              rw [nlenEq]
              simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "nlen" ≠ ofString "np" from by decide]

end InitECandidate.Solver.Input.CurrentStartup.RequestPositions

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestPositions.declared_exact
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestPositions.bindings
