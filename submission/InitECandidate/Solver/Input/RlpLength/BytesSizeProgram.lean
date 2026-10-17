import InitECandidate.Solver.Input.RlpLength.ScalarSizes

namespace InitECandidate.Solver.Input.RlpLength.BytesSize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_bytes_encoded_len with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "first_byte",.one),(ofString "n",.one)]
def condition : ExpHOL 64 := .op .and
  [.cmp .notEqual (.const 0#64) (.cmp .equal (localVar "n") (.const 1#64)),
   .cmp .notEqual (.const 0#64) (.cmp .lower (localVar "first_byte") (.const 128#64))]
def returnSize : ProgHOL 64 := .return (.op .add [localVar "h",localVar "n"])
def longTail : ProgHOL 64 := .decCall (ofString "h") .one (ofString "rlp_header_len") [localVar "n"] returnSize

theorem body_shape : body=.seq (shortGuard condition) longTail := by
  simp only [body,Guest.guestFn_rlp_bytes_encoded_len,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    shortGuard,condition,longTail,returnSize,localVar]

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64)
    (fb : source.locals.lookup (ofString "first_byte")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n))) :
    eval source condition=some (.val (.word (if n=1#64 ∧ first.toNat<128 then 1#64 else 0#64))) := by
  by_cases one : n=1#64 <;> by_cases small : first.toNat<128
  all_goals simp [eval,condition,localVar,evalHOLExact,evalListHOLExact,toExact,fb,len,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,one,small,valueIsWord,valueWord,wordOpHOL,wordOp]
  all_goals decide

def rawLocals (first n : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "n" then some (.val (.word n)) else if name=ofString "first_byte" then some (.val (.word first)) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (first n : BitVec 64)
    (lookup : codeFn (ofString "rlp_bytes_encoded_len")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn (ofString "rlp_bytes_encoded_len") [.val (.word first),.val (.word n)]=some (body,callee,.one) ∧
      callee.lookup (ofString "first_byte")=some (.val (.word first)) ∧ callee.lookup (ofString "n")=some (.val (.word n)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=([.val (.word first),.val (.word n)] : List (ValueHOL 64)).length ∧
      ((formals.zip [.val (.word first),.val (.word n)]).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "rlp_bytes_encoded_len") [.val (.word first),.val (.word n)]=some (body,rawLocals first n,.one) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals rw [locals]
  · simp [rawLocals,show ofString "first_byte"≠ofString "n" from by decide]
  · simp [rawLocals]

end InitECandidate.Solver.Input.RlpLength.BytesSize

#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.body_shape
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.condition_read
#print axioms InitECandidate.Solver.Input.RlpLength.BytesSize.environment
