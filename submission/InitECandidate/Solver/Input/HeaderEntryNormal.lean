import InitECandidate.Solver.Input.HeaderEntry

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A genuine normal return of the fixed decoder establishes the actual schema
and minimum copied extent and exposes its actual shifted first-container tail. -/
theorem normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 (input.length%2^64)))))
    (code : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    18≤input.length%2^64 ∧ Guest.GasLimit.byte input 0=21 ∧ Guest.GasLimit.byte input 1=1 ∧
      evaluateHOLFiniteState (shifted source pointer (input.length%2^64)) afterHeader=(some (.returned value),post) := by
  rw [entry_execute source input pointer heap pointerLocal lengthLocal code exceptionShape enough] at run
  by_cases short : input.length%2^64<2
  · simp only [if_pos short] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · simp only [if_neg short] at run
    by_cases wrong : Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1
    · simp only [if_pos wrong] at run
      have impossible:=congrArg Prod.fst run
      cases impossible
    · simp only [if_neg wrong] at run
      by_cases small : input.length%2^64<18
      · simp only [if_pos small] at run
        have impossible:=congrArg Prod.fst run
        cases impossible
      · simp only [if_neg small] at run
        have schema : Guest.GasLimit.byte input 0=21 ∧ Guest.GasLimit.byte input 1=1 := by
          simpa only [not_or,not_not] using wrong
        exact ⟨by omega,schema.1,schema.2,run⟩

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.normal_entry
