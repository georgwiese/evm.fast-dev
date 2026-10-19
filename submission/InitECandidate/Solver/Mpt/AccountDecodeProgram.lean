import InitECandidate.Solver.Rlp.SlicesProgram
import InitECandidate.Solver.Rlp.DecodeCost
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private def decBody : ProgHOL 64 → ProgHOL 64 | .dec _ _ _ rest=>rest | _=>.skip
private def callBody : ProgHOL 64 → ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def seqFirst : ProgHOL 64 → ProgHOL 64 | .seq first _=>first | _=>.skip
private def seqRest : ProgHOL 64 → ProgHOL 64 | .seq _ rest=>rest | _=>.skip

def body : ProgHOL 64 := match Guest.guestFn_decode_account_from_leaf with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS × ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "acct_out",.one)]
def fail (error : BitVec 64) : ProgHOL 64 := .call (some (none,none)) (ofString "mpt_fail") [.const error]
def field (name : String) (index : Nat) : ExpHOL 64 := .rfield index (localVar name)
def decodeArguments : List (ExpHOL 64) := [localVar "p",localVar "n"]
def handler : ProgHOL 64 := fail 20#64
def caught : ProgHOL 64 := .call (some (some (.local,ofString "it"),some (ofString "RlpErr",ofString "e",handler)))
  (ofString "rlp_decode_fully") decodeArguments
def afterDecode : ProgHOL 64 := seqRest (decBody (decBody body))
def afterSlices : ProgHOL 64 := callBody (seqRest afterDecode)
def fields : ProgHOL 64 := decBody (seqRest afterSlices)
def afterFields : ProgHOL 64 := callBody (callBody (callBody (callBody fields)))
def nonceDeclarations : ProgHOL 64 := seqRest (seqRest afterFields)
def nonceLoop : ProgHOL 64 := seqFirst (decBody (decBody nonceDeclarations))
def afterNonce : ProgHOL 64 := seqRest (decBody (decBody nonceDeclarations))
def nonceLoopBody : ProgHOL 64 := match nonceLoop with | .while _ loopBody=>loopBody | _=>.skip
def balancePhase : ProgHOL 64 := seqRest (seqRest afterNonce)
def balanceLoop : ProgHOL 64 := seqFirst (seqRest (seqRest balancePhase))
def afterBalance : ProgHOL 64 := seqRest (seqRest (seqRest balancePhase))
def balanceLoopBody : ProgHOL 64 := match balanceLoop with | .while _ loopBody=>loopBody | _=>.skip
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def nonceAccumulate : ProgHOL 64 := .assign .local (ofString "nonce")
  (.op .or [.shift .lsl (localVar "nonce") (.const 8#64),.loadByte (.op .add [field "f0" 1,localVar "i"])])
def balanceStore : ProgHOL 64 := .store (localVar "lp") (.op .or
  [.load .one (localVar "lp"),.shift .lsl (.loadByte (.op .add [field "f1" 1,localVar "i"]))
    (.panop .mul [.op .and [localVar "pos",.const 7#64],.const 8#64])])
def fieldArguments (index : Nat) : List (ExpHOL 64) :=
  [.load .one (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64]]),
    .load .one (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64],.const 8#64])]

set_option maxRecDepth 10000
theorem body_shape : body=.dec (ofString "it") Rlp.Item.resultShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
    (.dec (ofString "e") .one (.const 0#64) (.seq caught afterDecode)) := by
  simp only [body,afterDecode,seqRest,decBody,caught,handler,fail,decodeArguments,Rlp.Item.resultShape,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem after_decode_shape : afterDecode=.seq (.ite (.cmp .notEqual (field "it" 0) (.const 1#64)) (fail 20#64) .skip)
    (.decCall (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") [field "it" 1,field "it" 2] afterSlices) := by
  simp only [afterDecode,afterSlices,body,seqRest,decBody,callBody,field,fail,Rlp.Slices.resultShape,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem after_slices_shape : afterSlices=.seq (.ite (.cmp .notEqual (field "sl" 1) (.const 4#64)) (fail 20#64) .skip)
    (.dec (ofString "arr") .one (field "sl" 0)
      (.decCall (ofString "f0") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 0)
        (.decCall (ofString "f1") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 1)
          (.decCall (ofString "f2") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 2)
            (.decCall (ofString "f3") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 3) afterFields))))) := by
  simp only [afterSlices,afterDecode,afterFields,fields,body,seqRest,decBody,callBody,field,fieldArguments,fail,Rlp.Item.resultShape,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem fields_shape : fields=
    .decCall (ofString "f0") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 0)
      (.decCall (ofString "f1") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 1)
        (.decCall (ofString "f2") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 2)
          (.decCall (ofString "f3") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 3) afterFields))) := by
  simp only [fields,afterSlices,afterDecode,afterFields,body,seqRest,decBody,callBody,fieldArguments,Rlp.Item.resultShape,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem after_fields_shape : afterFields=.seq
    (.ite (.cmp .notEqual (.op .or [field "f0" 0,field "f1" 0,field "f2" 0,field "f3" 0]) (.const 0#64)) (fail 20#64) .skip)
    (.seq (.ite (.cmp .lower (.const 8#64) (field "f0" 2)) (fail 21#64) .skip)
      (.dec (ofString "nonce") .one (.const 0#64) (.dec (ofString "i") .one (.const 0#64) (.seq nonceLoop afterNonce)))) := by
  simp only [afterFields,fields,afterSlices,afterDecode,nonceLoop,afterNonce,nonceDeclarations,body,seqRest,seqFirst,decBody,callBody,field,fail,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem nonce_loop_shape : nonceLoop=.while (.cmp .lower (localVar "i") (field "f0" 2)) nonceLoopBody := by
  simp only [nonceLoop,nonceLoopBody,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,field,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem balance_loop_shape : balanceLoop=.while (.cmp .lower (localVar "i") (field "f1" 2)) balanceLoopBody := by
  simp only [balanceLoop,balanceLoopBody,balancePhase,afterNonce,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,field,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem nonce_body_shape : nonceLoopBody=.seq nonceAccumulate increment := by
  simp only [nonceLoopBody,nonceLoop,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,
    nonceAccumulate,increment,field,localVar,Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem balance_body_shape : balanceLoopBody=
    .dec (ofString "pos") .one (.op .sub [.op .sub [field "f1" 2,.const 1#64],localVar "i"])
      (.dec (ofString "lp") .one (.op .add [localVar "acct_out",.const 8#64,.panop .mul [.shift .lsr (localVar "pos") (.const 3#64),.const 8#64]])
        (.seq balanceStore increment)) := by
  simp only [balanceLoopBody,balanceLoop,balancePhase,afterNonce,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,
    balanceStore,increment,field,localVar,Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem after_nonce_shape : afterNonce=.seq (.store (.op .add [localVar "acct_out",.const 0#64]) (localVar "nonce"))
    (.seq (.ite (.cmp .lower (.const 32#64) (field "f1" 2)) (fail 22#64) .skip) balancePhase) := by
  simp only [afterNonce,balancePhase,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,field,fail,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem balance_phase_shape : balancePhase=.seq
    (.call (some (none,none)) (ofString "memzero") [.op .add [localVar "acct_out",.const 8#64],.const 32#64])
    (.seq (.assign .local (ofString "i") (.const 0#64)) (.seq balanceLoop afterBalance)) := by
  simp only [balancePhase,balanceLoop,afterBalance,afterNonce,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,field,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem after_balance_shape : afterBalance=.seq
    (.ite (.cmp .equal (field "f2" 2) (.const 0#64))
      (.store (.op .add [localVar "acct_out",.const 40#64]) (.var .global (ofString "empty_trie_root")))
      (.seq (.ite (.cmp .notEqual (field "f2" 2) (.const 32#64)) (fail 23#64) .skip)
        (.store (.op .add [localVar "acct_out",.const 40#64]) (field "f2" 1))))
    (.seq (.ite (.cmp .equal (field "f3" 2) (.const 0#64))
      (.store (.op .add [localVar "acct_out",.const 48#64]) (.var .global (ofString "empty_code_hash")))
      (.seq (.ite (.cmp .notEqual (field "f3" 2) (.const 32#64)) (fail 24#64) .skip)
        (.store (.op .add [localVar "acct_out",.const 48#64]) (field "f3" 1)))) (.return (.const 0#64))) := by
  simp only [afterBalance,balancePhase,afterNonce,nonceDeclarations,afterFields,fields,afterSlices,afterDecode,body,seqRest,seqFirst,decBody,callBody,field,fail,localVar,
    Guest.guestFn_decode_account_from_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "decode_account_from_leaf")=some (formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 269 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_decode_account_from_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.guestFn_decode_account_from_leaf,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_decode_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_slices_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.fields_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_loop_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_loop_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_body_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_body_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_nonce_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.balance_phase_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_balance_shape
#print axioms InitECandidate.Solver.Mpt.AccountDecode.original_code
