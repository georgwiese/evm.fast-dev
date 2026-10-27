import InitECandidate.Solver.Input.HeaderProgram
import InitECandidate.Solver.Input.StoreScalar64

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prefixBody : ProgHOL 64 := Header.continuation
def requestBody : ProgHOL 64 := match prefixBody with
  | .dec _ _ _ (.dec _ _ _ (.decCall _ _ _ _ (.seq _ (.dec _ _ _ (.dec _ _ _ (.seq _ rest))))))=>rest
  | _=>.skip
def continuation : ProgHOL 64 := match requestBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ rest))))))=>rest
  | _=>.skip
def chainStore : ProgHOL 64 := .store (Scalar.plus (localVar "si") 88) (Scalar.flat64 (localVar "p") [8])
def pointerExpression : ExpHOL 64 := .op .add [localVar "p",localVar "o_npr"]
def lengthExpression : ExpHOL 64 := .op .sub [localVar "o_wit",localVar "o_npr"]
def lengthTest : ExpHOL 64 := .cmp .lower (localVar "nlen") (.const 44#64)
def lengthGuard : ProgHOL 64 := .ite lengthTest (.call (some (none,none)) (ofString "ssz_fail") [.const 81#64]) .skip
def storePayload : ProgHOL 64 := .store Header.offsets (localVar "o_pl")
def storeHashes : ProgHOL 64 := .store (Scalar.plus Header.offsets 8) (localVar "o_vh")
def storeRequests : ProgHOL 64 := .store (Scalar.plus Header.offsets 16) (localVar "o_rq")
def guardArguments : List (ExpHOL 64) := [Header.offsets,.const 3#64,.const 44#64,localVar "nlen"]
def guardCall : ProgHOL 64 := .call (some (none,none)) (ofString "ssz_check_offsets") guardArguments

theorem prefix_shape : prefixBody=.dec (ofString "o_npr") .one (.load .one Header.offsets)
    (.dec (ofString "o_wit") .one (.load .one (Scalar.plus Header.offsets 8))
      (.decCall (ofString "si") .one (ofString "alloc") [.const 96#64]
        (.seq chainStore (.dec (ofString "np") .one pointerExpression
          (.dec (ofString "nlen") .one lengthExpression (.seq lengthGuard requestBody)))))) := by
  simp only [prefixBody,requestBody,Header.continuation,Header.afterHeader,Header.body,Guest.Software.guestFn_decode_stateless_input,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Header.offsets,localVar,chainStore,
    Scalar.plus,Scalar.flat64,Scalar.flat32,Scalar.flatAddress,Scalar.shift,pointerExpression,lengthExpression,lengthGuard,lengthTest,
    List.nil_append,List.cons_append,List.append_nil]

theorem request_shape : requestBody=.dec (ofString "o_pl") .one (Scalar.flat32 (localVar "np") [])
    (.dec (ofString "o_vh") .one (Scalar.flat32 (localVar "np") [4])
      (.dec (ofString "o_rq") .one (Scalar.flat32 (localVar "np") [40])
        (.seq storePayload (.seq storeHashes (.seq storeRequests (.seq guardCall continuation)))))) := by
  simp only [requestBody,prefixBody,Header.continuation,Header.afterHeader,Header.body,continuation,Guest.Software.guestFn_decode_stateless_input,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Header.offsets,localVar,
    Scalar.plus,Scalar.flat32,Scalar.flatAddress,Scalar.shift,storePayload,storeHashes,storeRequests,guardCall,guardArguments,
    List.nil_append,List.cons_append,List.append_nil]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.prefix_shape
#print axioms InitECandidate.Solver.Input.Request.request_shape
