import Guest.SoftwareAst
import InitECandidate.Solver.Input.StoreScalar
import InitECandidate.Solver.Input.OffsetsCallNormal

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_decode_stateless_input with
  | .function fn=>progToHOL fn.body | _=>.skip
def afterHeader : ProgHOL 64 := match body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ rest))))=>rest | _=>.skip
def continuation : ProgHOL 64 := match afterHeader with
  | .seq _ (.seq _ (.seq _ rest))=>rest | _=>.skip
def offsets : ExpHOL 64 := .var .global (ofString "ssz_offs")
def storeFirst : ProgHOL 64 := .store offsets (Scalar.flat32 (localVar "p") [])
def storeSecond : ProgHOL 64 := .store (Scalar.plus offsets 8) (Scalar.flat32 (localVar "p") [4])
def guardArguments : List (ExpHOL 64) := [offsets,.const 2#64,.const 16#64,localVar "len"]
def guardCall : ProgHOL 64 := .call (some (none,none)) (ofString "ssz_check_offsets") guardArguments

theorem after_header_shape : afterHeader=.seq storeFirst (.seq storeSecond (.seq guardCall continuation)) := by
  simp only [afterHeader,body,continuation,Guest.Software.guestFn_decode_stateless_input,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,storeFirst,storeSecond,offsets,guardCall,guardArguments,
    Scalar.flat32,Scalar.flatAddress,Scalar.plus,Scalar.shift,localVar,List.nil_append,List.cons_append,List.append_nil]

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.after_header_shape
