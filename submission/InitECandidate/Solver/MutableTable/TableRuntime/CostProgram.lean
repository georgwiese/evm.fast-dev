import InitECandidate.Solver.WitnessRadix.TableNewProgram
import InitECandidate.Solver.Input.ClockCostScopeLocals
import InitECandidate.Solver.Input.ZeroAnyCost

namespace InitECandidate.Solver.MutableTable.TableRuntime.Cost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Action where
  | allocation (name : String) (amount : ExpHOL 64)
  | declaration (name : String) (value : ExpHOL 64)
  | store (address value : ExpHOL 64)
  | clear

def clear : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "used",localVar "cap"]
def program : List Action→ProgHOL 64
  | []=>TableNew.returnTable
  | .allocation name amount::rest=>.decCall (ofString name) .one (ofString "alloc") [amount] (program rest)
  | .declaration name value::rest=>.dec (ofString name) .one value (program rest)
  | .store address value::rest=>.seq (.store address value) (program rest)
  | .clear::rest=>.seq clear (program rest)
def actions : List Action:=
  [.allocation "t" (.const 72#64),.declaration "stride" TableNew.stride,
    .store (addConst (localVar "t") 0#64) (localVar "key_len"),
    .store (addConst (localVar "t") 8#64) (localVar "stride"),
    .store (addConst (localVar "t") 16#64) (localVar "cap"),
    .store (addConst (localVar "t") 24#64) (.const 0#64),
    .allocation "keys" (TableNew.capacityTimes (localVar "stride")),
    .store (addConst (localVar "t") 32#64) (localVar "keys"),
    .allocation "vals" (TableNew.capacityTimes (.const 8#64)),
    .store (addConst (localVar "t") 40#64) (localVar "vals"),
    .allocation "used" (localVar "cap"),.clear,
    .store (addConst (localVar "t") 48#64) (localVar "used"),
    .allocation "order" (TableNew.capacityTimes (.const 8#64)),
    .store (addConst (localVar "t") 56#64) (localVar "order"),
    .allocation "order_pos" (TableNew.capacityTimes (.const 8#64)),
    .store (addConst (localVar "t") 64#64) (localVar "order_pos")]

theorem body_shape : TableNew.body=program actions:=by
  rw [TableNew.body_shape]
  simp only [TableNew.actions,TableNew.headerStore,ProgramPrefix.program,program,actions,clear]

def Valid : List String→List Action→Prop
  | _,[]=>True
  | names,.allocation name _::rest | names,.declaration name _::rest=>ofString name≠ofString "cap" ∧ Valid (name::names) rest
  | names,.store ..::rest=>Valid names rest
  | names,.clear::rest=>"used"∈names ∧ Valid names rest

theorem actions_valid : Valid [] actions:=by
  simp only [actions,Valid]
  decide

def price (capacity : Nat) : List Action→Nat
  | []=>0
  | .allocation ..::rest=>2+price capacity rest
  | .declaration ..::rest | .store ..::rest=>price capacity rest
  | .clear::rest=>Input.ZeroAny.price capacity+1+price capacity rest

theorem actions_price (capacity : Nat) : price capacity actions=Input.ZeroAny.price capacity+13:=by
  simp only [price,actions]
  omega

def Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : Nat) (names : List String) : Prop:=
  source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 capacity))) ∧
    ∀ name∈names,∃ word,source.locals.lookup (ofString name)=some (.val (.word word))

theorem Locals.of_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : Nat) (names : List String)
    (locals : Locals source capacity names) (same : ∀ key,target.locals.lookup key=source.locals.lookup key) : Locals target capacity names:=
  ⟨(same _).trans locals.1,fun name member=>by obtain ⟨word,cell⟩:=locals.2 name member; exact ⟨word,(same _).trans cell⟩⟩

theorem Locals.bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : Nat) (names : List String)
    (locals : Locals source capacity names) (name : String) (word : BitVec 64) (other : ofString name≠ofString "cap") :
    Locals (QueryBranch.bind source name word) capacity (name::names):=by
  refine ⟨(bind_lookup_other source name "cap" word other).trans locals.1,?_⟩
  intro query member
  by_cases equal : ofString query=ofString name
  · exact ⟨word,by rewrite [equal]; exact bind_lookup_same _ _ _⟩
  · have oldMember : query∈names:=by rcases List.mem_cons.mp member with same|member; exact (equal (congrArg ofString same)).elim; exact member
    obtain ⟨value,cell⟩:=locals.2 query oldMember
    exact ⟨value,(bind_lookup_other source name query word (Ne.symm equal)).trans cell⟩

end InitECandidate.Solver.MutableTable.TableRuntime.Cost

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.body_shape
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.actions_valid
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.actions_price
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.Locals.of_agreement
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.Locals.bind
