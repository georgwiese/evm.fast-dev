import InitECandidate.Solver.CurrentKeccak.PermutationMemory
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.Input.MemoryNormal

namespace InitECandidate.Solver.CurrentKeccak.Permutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

private def values (stp : BitVec 64) : List (ValueHOL 64) := [.val (.word stp)]
private def rawLocals (stp : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "stp" then some (.val (.word stp)) else none

/-- The genuine one-word ABI supplies all scalar callee locals, rather
than assuming local types at a future store. -/
theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (stp : BitVec 64)
    (code : codeFn (ofString "keccak_f1600")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "keccak_f1600") (values stp)=some (body,callee,.one) ∧
      callee.lookup=rawLocals stp := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values stp).length ∧
      ((formals.zip (values stp)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "keccak_f1600") (values stp)=some (body,rawLocals stp,.one) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  exact CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw

/-- Lift the actual25-lane memory frame through its real ordinary caller.
No restriction on the caller's other locals or a future successful round. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64)
    (installed : OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word stp)])
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_f1600") arguments)=(none,post)) :
    post.memory query=source.memory query := by
  obtain ⟨callee,called,locals⟩:=environment source.code.lookup stp (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have ready : ScalarLocals.Words entry := by
    intro name value found
    change callee.lookup name=some value at found
    rw [locals] at found
    by_cases same : name=ofString "stp"
    · exact ⟨stp,by simpa [rawLocals,same] using found.symm⟩
    · simp [rawLocals,same] at found
  have cell : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) := by
    change callee.lookup _=_
    rw [locals]
    simp [rawLocals]
  apply MemoryAt.call_normal source post _ arguments (values stp) body callee .one query args called ?_ run
  intro target value bodyRun
  exact body_memory entry target stp query ready cell away value bodyRun

end InitECandidate.Solver.CurrentKeccak.Permutation

#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.environment
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.call_memory
