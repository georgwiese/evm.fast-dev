import InitECandidate.Solver.Mpt.StateInitStorageProgram
import InitECandidate.Solver.MutableTable.TableRuntime.Budget

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack Flapjack.Pancake.PanLang WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Action where
  | table (kind : KeyHash.Kind) (bits offset : Nat)
  | scalar (offset : Nat) (value : BitVec 64)
  deriving DecidableEq

def tableArguments (kind : KeyHash.Kind) (bits : Nat) : List (ExpHOL 64):=
  [.const (BitVec.ofNat 64 (KeyHash.keySize kind)),.const (BitVec.ofNat 64 (2^bits))]
def tableCall (kind : KeyHash.Kind) (bits : Nat) : ProgHOL 64:=
  .call (some (some (.local,ofString "t"),none)) (ofString "htab_new") (tableArguments kind bits)
def fieldStore (offset : Nat) (value : ExpHOL 64) : ProgHOL 64:=.store (addConst (.var .global (ofString "bs")) (BitVec.ofNat 64 offset)) value
def program : List Action → ProgHOL 64 → ProgHOL 64
  | [],tail=>tail
  | .table kind bits offset::rest,tail=>.seq (tableCall kind bits) (.seq (fieldStore offset (localVar "t")) (program rest tail))
  | .scalar offset value::rest,tail=>.seq (fieldStore offset (.const value)) (program rest tail)
def drop : List Action → ProgHOL 64 → ProgHOL 64
  | [],tail=>tail
  | .table ..::rest,.seq _ (.seq _ tail)=>drop rest tail
  | .scalar ..::rest,.seq _ tail=>drop rest tail
  | _,_=>.skip
def actions : List Action:=
  [.table .account 8 8,.table .account 8 16,.table .storage 8 24,.table .account 6 32,
    .table .storage 6 40,.table .word 6 48,.scalar 56 0#64,.scalar 64 0#64,.table .account 8 72]
def allocate : ProgHOL 64:=.call (some (some (.global,ofString "bs"),none)) (ofString "alloc") [.const 80#64]
def storeWorkspace : ProgHOL 64:=fieldStore 0 (.var .global (ofString "ws"))
def afterAllocation : ProgHOL 64:=match afterStorageTrie with | .seq _ tail=>tail | _=>.skip
def afterWorkspace : ProgHOL 64:=match afterAllocation with | .seq _ tail=>tail | _=>.skip
def afterFields : ProgHOL 64:=drop actions afterWorkspace

set_option maxRecDepth 100000 in
/-- Literal original322 block-state allocation, workspace link and every
actual table/ancestor-field write, ending at the unchanged sk_buf suffix. -/
theorem shapes : afterStorageTrie=.seq allocate afterAllocation ∧
    afterAllocation=.seq storeWorkspace afterWorkspace ∧ afterWorkspace=program actions afterFields := by
  simp only [afterStorageTrie,afterStorageTable,afterRootStore,afterRoot,rootCall,afterSecond,afterFirst,afterAllocation,
    StateInit.afterAllocation,body,Guest.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    allocate,storeWorkspace,afterWorkspace,program,actions,afterFields,drop,tableCall,tableArguments,fieldStore,localVar,addConst,KeyHash.keySize]
  trivial

def Action.Valid : Action → Prop
  | .table _ bits offset=>3≤bits ∧ bits≤8 ∧ offset+8≤80 ∧ offset%8=0
  | .scalar offset _=>offset+8≤80 ∧ offset%8=0

theorem actions_valid : ∀ action∈actions,action.Valid:=by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold Action.Valid <;> decide

def price : List Action → Nat
  | []=>0
  | .table _ bits _::rest=>TableRuntime.price (2^bits)+1+price rest
  | .scalar ..::rest=>price rest
def cursor (start : Nat) : List Action → Nat
  | []=>start
  | .table kind bits _::rest=>cursor (NaturalLayout.freshEnd kind start (2^bits)) rest
  | .scalar ..::rest=>cursor start rest

theorem price_all : price actions=94:=by decide
theorem cursor_all (start : Nat) : cursor start actions=start+70840:=by
  simp only [cursor,actions,NaturalLayout.freshEnd,NaturalLayout.stride,NaturalLayout.rounded,KeyHash.keySize]
  omega

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.shapes
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.actions_valid
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.price_all
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.cursor_all
