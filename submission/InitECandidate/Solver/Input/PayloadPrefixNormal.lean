import InitECandidate.Solver.Input.PayloadOffsetsNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Actual four lexical bindings after the payload prefix. -/
theorem declared_offsets (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (declaredState source input).locals.lookup (ofString "o_extra")=some (.val (.word (offsetWords input 0))) ∧
    (declaredState source input).locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))) ∧
    (declaredState source input).locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))) ∧
    (declaredState source input).locals.lookup (ofString "o_bal")=some (.val (.word (offsetWords input 3))) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (bind_lookup_other (wdState source input) "o_bal" "o_extra" _ (by decide)).trans ((bind_lookup_other (txState source input) "o_wd" "o_extra" _ (by decide)).trans ((bind_lookup_other (extraState source input) "o_txs" "o_extra" _ (by decide)).trans (bind_lookup_same _ _ _)))
  · exact (bind_lookup_other (wdState source input) "o_bal" "o_txs" _ (by decide)).trans ((bind_lookup_other (txState source input) "o_wd" "o_txs" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other (wdState source input) "o_bal" "o_wd" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

theorem declared_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (name : String)
    (e : ofString "o_extra"≠ofString name) (t : ofString "o_txs"≠ofString name) (w : ofString "o_wd"≠ofString name) (b : ofString "o_bal"≠ofString name) :
    (declaredState source input).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  exact (bind_lookup_other (wdState source input) "o_bal" name _ b).trans
    ((bind_lookup_other (txState source input) "o_wd" name _ w).trans
      ((bind_lookup_other (extraState source input) "o_txs" name _ t).trans (bind_lookup_other source "o_extra" name _ e)))

/-- Actual full allocation/header/declaration prefix exposes the real validator
body on a normal return, with copied bytes and no extra input-shape premise. -/
theorem prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64)
    (restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory→PanSemStateFiniteExact 64 Guest.HostMemory)
    (setup : Executes source prefixActions (prepared source input pointer cursor length) restoreStack)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    ∃ innerPost,evaluateHOLFiniteState (prepared source input pointer cursor length) offsetBody=(some (.returned value),innerPost) ∧ post=restoreStack innerPost := by
  have actual:=WitnessRadix.ProgramPrefix.execute setup offsetBody
  rw [←prefix_shape] at actual
  have result:=congrArg Prod.fst (actual.symm.trans run)
  exact ⟨(evaluateHOLFiniteState (prepared source input pointer cursor length) offsetBody).2,Prod.ext result rfl,
    (congrArg Prod.snd (actual.symm.trans run)).symm⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.declared_offsets
#print axioms InitECandidate.Solver.Input.Payload.declared_other
#print axioms InitECandidate.Solver.Input.Payload.prefix_normal
