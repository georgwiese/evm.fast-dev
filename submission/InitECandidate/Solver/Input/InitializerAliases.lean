import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.InitializerAliases
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Action where
  name : String
  offset : Nat
  expression : ExpHOL 64

def direct (base name : String) : Action := ⟨name,0,.var .global (ofString base)⟩
def offset (base name : String) (bytes : Nat) : Action := ⟨name,bytes,.op .add [.var .global (ofString base),.const (BitVec.ofNat 64 bytes)]⟩
def withTail : List Action → ProgHOL 64 → ProgHOL 64
  | [],tail => tail
  | action :: rest,tail => .seq (.assign .global (ofString action.name) action.expression) (withTail rest tail)
def reserve (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (action : Action) :=
  putGlobal source action.name (pointer + BitVec.ofNat 64 action.offset)
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : List Action → PanSemStateFiniteExact 64 Guest.HostMemory
  | [] => source
  | action :: rest => template (reserve source pointer action) pointer rest

structure Valid (base : String) (action : Action) : Prop where
  member : ofString action.name ∈ OriginalScalarGlobals.names
  different : ofString action.name ≠ ofString base
  read : ∀ (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64),
    source.globals.lookup (ofString base) = some (.val (.word pointer)) →
    QueryBranch.eval source action.expression = some (.val (.word (pointer + BitVec.ofNat 64 action.offset)))

theorem direct_valid (base name : String) (member : ofString name ∈ OriginalScalarGlobals.names) (different : ofString name ≠ ofString base) : Valid base (direct base name) := by
  refine ⟨member,different,?_⟩
  intro source pointer binding
  simpa [direct,QueryBranch.eval,evalHOLExact,toExact] using binding

theorem offset_valid (base name : String) (bytes : Nat) (member : ofString name ∈ OriginalScalarGlobals.names) (different : ofString name ≠ ofString base) : Valid base (offset base name bytes) := by
  refine ⟨member,different,?_⟩
  intro source pointer binding
  simp [offset,QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source pointer actions).globals := by
  induction actions generalizing source with
  | nil => exact scalars
  | cons action rest ih => exact ih (reserve source pointer action) (scalars.update (ofString action.name) _)

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) (clock : Nat) :
    template {source with clock := clock} pointer actions = {template source pointer actions with clock := clock} := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) :
    InitializerAllocations.context (template source pointer actions) = InitializerAllocations.context source := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact (ih (reserve source pointer action)).trans (by rfl)

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) (key : MlS)
    (different : ∀ action,action ∈ actions → key ≠ ofString action.name) :
    (template source pointer actions).globals.lookup key = source.globals.lookup key := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
    exact (ih (reserve source pointer action) (fun item member => different item (List.mem_cons_of_mem _ member))).trans
      (putGlobal.lookup_other source action.name _ key (different action (by simp)))

/-- Actual scalar global alias assignments, preserving the base binding and
all scalar destinations while resuming an arbitrary real continuation. -/
theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : String) (pointer : BitVec 64)
    (actions : List Action) (tail : ProgHOL 64) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (binding : source.globals.lookup (ofString base) = some (.val (.word pointer)))
    (valid : ∀ action,action ∈ actions → Valid base action) :
    evaluateHOLFiniteState source (withTail actions tail) = evaluateHOLFiniteState (template source pointer actions) tail := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
    have current := valid action (by simp)
    obtain ⟨old,present⟩ := scalars _ current.member
    have run := global_assign_execute source action.name old _ action.expression present (current.read source pointer binding)
    have nextBinding : (reserve source pointer action).globals.lookup (ofString base) = some (.val (.word pointer)) :=
      (putGlobal.lookup_other source action.name _ (ofString base) current.different.symm).trans binding
    rw [withTail,StateSteps.next_sequence source (reserve source pointer action) _ _ run (Nat.le_refl _)]
    exact ih (reserve source pointer action) (scalars.update (ofString action.name) _) nextBinding
      (fun item member => valid item (List.mem_cons_of_mem _ member))

end InitECandidate.Solver.Input.InitializerAliases

#print axioms InitECandidate.Solver.Input.InitializerAliases.direct_valid
#print axioms InitECandidate.Solver.Input.InitializerAliases.offset_valid
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_scalars
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_clock
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_context
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_other
#print axioms InitECandidate.Solver.Input.InitializerAliases.execute_prefix
