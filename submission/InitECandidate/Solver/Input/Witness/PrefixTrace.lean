import InitECandidate.Solver.Input.Witness.PrefixSetup
import InitECandidate.Solver.Input.SszGuardTrace

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

/-- Both real witness declarations and its original length guard, including
SszErr82. Actual non-timeout execution funds a rejection; the passing body
remains the real unchanged continuation, with no future return assumed. -/
theorem prefix_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (offset : Nat) (heap : Blob.HeapInput source input pointer)
    (extent : 2 ≤ input.length % 2^64) (offsetUpper : offset ≤ input.length % 2^64 - 2)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + 2#64))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))))
    (o : source.locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 offset))))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source prefixBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (input.length % 2^64 - 2 - offset < 12 ∧ result = some (.exception (ofString "SszErr") (.val (.word 82#64))) ∧ source.clock - post.clock ≤ 1) ∨
    (12 ≤ input.length % 2^64 - 2 - offset ∧
      Blob.HeapInput (prefixPrepared source input pointer offset) input pointer ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2+offset)))) ∧
      (prefixPrepared source input pointer offset).locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - offset)))) ∧
      ∃ innerPost,evaluateHOLFiniteState (prefixPrepared source input pointer offset) offsetBody = (result,innerPost) ∧ post = restorePrefix source pointer offset innerPost) := by
  obtain ⟨setup,bytes,wp,wlen⟩ := prefix_setup source input pointer offset heap extent offsetUpper p n o
  rw [prefix_shape,ProgramPrefix.execute setup (.seq shortGuard offsetBody)] at run
  let ready := prefixPrepared source input pointer offset
  let innerPost := (evaluateHOLFiniteState ready (.seq shortGuard offsetBody)).2
  have observed := congrArg Prod.fst run
  have remaining : evaluateHOLFiniteState ready (.seq shortGuard offsetBody) = (result,innerPost) := Prod.ext observed rfl
  have endpoint : post = restorePrefix source pointer offset innerPost := (congrArg Prod.snd run).symm
  have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
  have number : (BitVec.ofNat 64 (input.length % 2^64 - 2 - offset)).toNat = input.length % 2^64 - 2 - offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have readyLen : ready.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - offset)))) := wlen
  have test : eval ready (.cmp .lower (localVar "wlen") (.const 12#64)) = some (.val (.word (if input.length % 2^64 - 2 - offset < 12 then 1#64 else 0#64))) := by
    simp [eval,localVar,evalHOLExact,toExact,readyLen,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,number]
    have fits : input.length % 18446744073709551616 - 2 - offset < 18446744073709551616 := by omega
    rw [Nat.mod_eq_of_lt fits]
  rcases Header.guard_trace ready innerPost (.cmp .lower (localVar "wlen") (.const 12#64)) 82#64 (input.length % 2^64 - 2 - offset < 12) offsetBody
    test failCode shape result remaining notTimeout with rejected | normal
  · obtain ⟨short,funded,same,innerEq⟩ := rejected
    have clock : post.clock = source.clock - 1 := by rw [endpoint,innerEq]; rfl
    exact Or.inl ⟨short,same,by rw [clock]; omega⟩
  · obtain ⟨minimum,rest⟩ := normal
    exact Or.inr ⟨by omega,bytes,wp,wlen,innerPost,rest,endpoint⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.prefix_trace
