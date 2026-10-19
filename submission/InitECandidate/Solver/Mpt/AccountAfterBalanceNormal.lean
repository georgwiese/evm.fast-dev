import InitECandidate.Solver.Mpt.AccountReferenceChoice

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Both actual final reference choices derive their0/32 widths and exact
word writes. The complete normal suffix really returns0; all other state
fields are retained apart from the required local-scope clearing. -/
theorem after_balance_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out pointer2 header2 payload2 flag2 pointer3 header3 payload3 flag3 emptyRoot emptyHash : BitVec 64)
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (cell2 : source.locals.lookup (ofString "f2")=some (Rlp.Item.result pointer2 header2 payload2 flag2))
    (cell3 : source.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterBalance=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ (payload2=0#64 ∨ payload2=32#64) ∧ (payload3=0#64 ∨ payload3=32#64) ∧
      post=emptyLocalsHOLFinite {source with memory:=(StoreWord.put
        (StoreWord.put source.memory (out+40#64) (if payload2=0#64 then emptyRoot else pointer2+header2))
        (out+48#64) (if payload3=0#64 then emptyHash else pointer3+header3))} := by
  rw [after_balance_reference_shape] at normal
  obtain ⟨rootPost,rootRun,hashTail,cell3Eq⟩ :=
    (reference_choice_safe (ofString "f3") "f2" 40 "empty_trie_root" 23#64).normal_continue source post
      (.seq (referenceChoice "f3" 48 "empty_code_hash" 24#64) (.return (.const 0#64))) returned normal
  obtain ⟨rootWidth,rootEq⟩ := reference_choice_normal source rootPost out pointer2 header2 payload2 flag2 emptyRoot "f2" "empty_trie_root" 40 23#64
    outputCell cell2 rootGlobal installed rootRun
  have currentOutput : rootPost.locals.lookup (ofString "acct_out")=some (.val (.word out)) := by rw [rootEq]; exact outputCell
  have current3 : rootPost.locals.lookup (ofString "f3")=some (Rlp.Item.result pointer3 header3 payload3 flag3) := cell3Eq.trans cell3
  have currentHash : rootPost.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)) := by rw [rootEq]; exact hashGlobal
  have currentInstalled : Input.OriginalCode.Installed rootPost.code := by rw [rootEq]; exact installed
  obtain ⟨hashPost,hashRun,returnRun,locals⟩ :=
    (reference_choice_safe (ofString "acct_out") "f3" 48 "empty_code_hash" 24#64).normal_continue rootPost post (.return (.const 0#64)) returned hashTail
  obtain ⟨hashWidth,hashEq⟩ := reference_choice_normal rootPost hashPost out pointer3 header3 payload3 flag3 emptyHash "f3" "empty_code_hash" 48 24#64
    currentOutput current3 currentHash currentInstalled hashRun
  have actual := Input.return_normal hashPost post (.const 0#64) returned returnRun
  have read := actual.1
  change some (.val (.word 0#64))=some returned at read
  refine ⟨(Option.some.inj read).symm,rootWidth,hashWidth,?_⟩
  rw [actual.2,hashEq,rootEq]

theorem Output.references_window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root hash : BitVec 64) (output : Output out) :
    Rlp.Slices.Window source (emptyLocalsHOLFinite {source with memory:=StoreWord.put (StoreWord.put source.memory (out+40#64) root) (out+48#64) hash})
      out.toNat (out.toNat+56) := by
  intro query outside
  have first := output.outside_address out 40 (by decide) query outside
  have second := output.outside_address out 48 (by decide) query outside
  change StoreWord.put (StoreWord.put source.memory (out+40#64) root) (out+48#64) hash query=source.memory query
  simp only [StoreWord.put,if_neg first,if_neg second]

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_balance_normal
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Output.references_window
