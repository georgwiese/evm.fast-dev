import InitECandidate.Solver.Headers.FieldStore
import InitECandidate.Solver.Headers.DecodeCountProgram

namespace InitECandidate.Solver.Headers.Pipeline
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- A finite analysis reification of the original header field syntax.
The checked equality below retains the exact original scopes and leaves. -/
inductive Code where
  | done
  | returned
  | store (offset : Nat) (value : StoreValue) (rest : Code)
  | declare (slot : Slot) (kind : Helper.Kind) (index : Nat) (control : BitVec 64) (rest : Code)
  | assign (slot : Slot) (kind : Helper.Kind) (index : Nat) (control : BitVec 64) (rest : Code)
  | guard (slot : Slot) (maximum error : BitVec 64) (rest : Code)
  | choose (yes no rest : Code)

def arguments (kind : Helper.Kind) (index : Nat) (control : BitVec 64) : List (ExpHOL 64) :=
  if kind.ternary then [.var .local (ofString "arr"),.const (BitVec.ofNat 64 index),.const control]
  else [.var .local (ofString "arr"),.const (BitVec.ofNat 64 index)]
def assigned (slot : Slot) (kind : Helper.Kind) (index : Nat) (control : BitVec 64) : ProgHOL 64 :=
  .call (some (some (.local,slot.name),none)) kind.name (arguments kind index control)

def program : Code→ProgHOL 64
  | .done=>.skip
  | .returned=>.return (.var .local (ofString "h"))
  | .store offset value .done=>storeProgram offset value
  | .store offset value rest=>.seq (storeProgram offset value) (program rest)
  | .declare slot kind index control rest=>.decCall slot.name slot.shape kind.name (arguments kind index control) (program rest)
  | .assign slot kind index control .done=>assigned slot kind index control
  | .assign slot kind index control rest=>.seq (assigned slot kind index control) (program rest)
  | .guard slot maximum error rest=>.seq
      (.ite (.cmp .lower (.const maximum) (.rfield 1 (.var .local slot.name))) (.raise (ofString "HdrErr") (.const error)) .skip) (program rest)
  | .choose yes no rest=>.seq
      (.ite (.cmp .notEqual (.var .local (ofString "is_current")) (.const 0#64)) (program yes) (program no)) (program rest)

def bytesSet (index width offset : Nat) (rest : Code) : Code :=
  .assign .f .bytes index (BitVec.ofNat 64 width) (.store offset (.saved .f) rest)
def wordSet (index offset : Nat) (rest : Code) : Code :=
  .assign .w .word index 0#64 (.store offset (.saved .w) rest)
def u256Set (index offset : Nat) (rest : Code) : Code :=
  .assign .d .u256 index 0#64 (.store offset (.saved .d) rest)
def uintSet (index : Nat) (rest : Code) : Code := .assign .bg .uint index 8#64 rest

def final : Code := .choose
  (bytesSet 21 32 232 (uintSet 22 (wordSet 22 240 .done)))
  (.store 232 .zero (.store 240 .zero .done)) .returned

def afterBg : Code := wordSet 17 200 (uintSet 18 (wordSet 18 208 (bytesSet 19 32 216 (bytesSet 20 32 224 final))))
def afterEx : Code := .store 128 (.part .ex 0) (.store 136 (.part .ex 1)
  (bytesSet 13 32 144 (bytesSet 14 8 152 (u256Set 15 160 (bytesSet 16 32 192 (.declare .bg .uint 17 8#64 afterBg))))))
def afterTsf : Code := .guard .tsf 8#64 12#64 (wordSet 11 120 (.declare .ex .raw 12 0#64 afterEx))
def afterW : Code := .store 96 (.saved .w) (wordSet 9 104 (wordSet 10 112 (.declare .tsf .uint 11 32#64 afterTsf)))
def afterD : Code := .store 64 (.saved .d) (.declare .w .word 8 0#64 afterW)
def afterF : Code := .store 8 (.saved .f)
  (bytesSet 1 32 16 (bytesSet 2 20 24 (bytesSet 3 32 32 (bytesSet 4 32 40
    (bytesSet 5 32 48 (bytesSet 6 256 56 (.declare .d .u256 7 0#64 afterD)))))))
def fields : Code := .store 0 .current (.declare .f .bytes 0 32#64 afterF)

set_option maxRecDepth 100000 in
/-- Exact unchanged decode_header210 field pipeline, including all six
real helper scopes, assigned reuse, integer-length guard and21/23 tail. -/
theorem original_fields : Decode.afterAllocation=program fields := by
  simp only [Decode.afterAllocation,Decode.afterCount,Decode.afterCurrent,Decode.afterList,Decode.afterKind,Decode.afterTop,Decode.body,
    program,fields,afterF,afterD,afterW,afterTsf,afterEx,afterBg,final,bytesSet,wordSet,u256Set,uintSet,
    assigned,arguments,storeProgram,storeAddress,StoreValue.expression,Slot.name,Slot.shape,Helper.Kind.name,Helper.Kind.ternary,Field.Kind.name,
    Input.RlpWrite.U256Value.tupleShape,Input.ScalarPair.tupleShape,
    Guest.guestFn_decode_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,Bool.false_eq_true,Bool.true_eq,WitnessRadix.QueryBranch.localVar,↓reduceIte]

end InitECandidate.Solver.Headers.Pipeline

#print axioms InitECandidate.Solver.Headers.Pipeline.original_fields
