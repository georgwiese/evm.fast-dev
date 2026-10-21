import InitECandidate.Solver.Input.LocalLoopSummary

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Local summaries through an actual declaration, including failed reads
and checks. The saved binding and ordinary control results are derived from
the body at its real declaration state. -/
theorem local_summary_declaration {F : Type} (key name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (other : key≠name) (summary : ∀ source : PanSemStateFiniteExact 64 F,LocalSummary key body source)
    (source : PanSemStateFiniteExact 64 F) : LocalSummary key (.dec name shape expression body) source := by
  classical
  unfold LocalSummary
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · split
    · rename_i value read checked
      let entry:=setVarHOLFinite name value source
      have info:=summary entry
      unfold LocalSummary at info
      generalize computed : evaluateHOLFiniteState entry body=output at info ⊢
      obtain ⟨result,inner⟩:=output
      dsimp only
      refine ⟨?_,info.2⟩
      intro normal
      have localFrame:=info.1 normal
      have entryCell : entry.locals.lookup key=source.locals.lookup key:=by
        simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
      change (inner.locals.resVarEq (name,source.locals.lookup name)).lookup key=source.locals.lookup key
      rw [lookup_resVarEq_toExact]
      cases saved : source.locals.lookup name <;> simpa [resVarHOLExact,FUPDATE,FDOMSUB,other] using localFrame.trans entryCell
    · simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.local_summary_declaration
