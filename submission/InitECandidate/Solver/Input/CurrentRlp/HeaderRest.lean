import InitECandidate.Solver.Input.CurrentRlp.HeaderOptional

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderRest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding HeaderFields

theorem budgets : sizes baseRest=816 ∧ costs baseRest=1188:=by decide

theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤50)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source (fields baseRest afterBase)).2.clock≤1291 := by
  have price:=fields_cost source original header buffer baseRest position context installed bounded facts (by rw [budgets.1]; omega)
    p afterBase 103 (by
      intro current finalPosition nextLower nextUpper reached
      have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
      have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
      exact HeaderOptional.cost current original header buffer finalPosition reached.context currentInstalled bounded optional
        (by omega) (by rw [budgets.1] at nextUpper; omega) reached.pointer currentBuf)
  rw [budgets.2] at price
  exact price

theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64) (position : Nat)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (lower : 9≤position) (upper : position≤50)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer position))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source (fields baseRest afterBase)=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  obtain ⟨current,finalPosition,nextLower,nextUpper,reached,remaining⟩:=fields_returned source target original header buffer baseRest position
    context installed bounded facts (by rw [budgets.1]; omega) p afterBase value returned
  have currentInstalled : OriginalCode.Installed current.code:=by rw [MemoryMetadata.code reached.metadata]; exact installed
  have currentBuf:=(reached.locals "buf" (by decide) (by decide)).trans buf
  obtain ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩:=HeaderOptional.normal current target original header buffer finalPosition
    reached.context currentInstalled bounded optional (by omega) (by rw [budgets.1] at nextUpper; omega) reached.pointer currentBuf value remaining
  exact ⟨start,encoded,positive,size,answer,arena,metadata.trans reached.metadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderRest

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.budgets
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderRest.normal
