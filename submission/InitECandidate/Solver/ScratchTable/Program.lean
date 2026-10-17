import InitECandidate.Solver.Arenas.DownPlan
import InitECandidate.Solver.Arenas.PrefixFields
import InitECandidate.Solver.WitnessRadix.TableNewProgram
import InitECandidate.Solver.WitnessRadix.ZeroSmallCall

namespace InitECandidate.Solver.ScratchTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix (Action)

def cursor (scratch : BitVec 64) (consumed : Nat) : BitVec 64 := scratch - BitVec.ofNat 64 consumed

def headerFields : List FieldStores.Field :=
  [⟨0, .saved "key_len" 20#64⟩, ⟨8, .saved "stride" 24#64⟩, ⟨16, .saved "cap" 4#64⟩, ⟨24, .literal 0#64⟩]
def pointerFields (offset : Nat) (name : String) (pointer : BitVec 64) : List FieldStores.Field := [⟨offset, .saved name pointer⟩]
def firstActions : List Action :=
  [.allocate "t" (.const 72#64), .declare "stride" WitnessRadix.TableNew.stride] ++
    Arenas.Prefix.fieldActions "t" "unused" headerFields
def middleActions : List Action :=
  [.allocate "keys" (WitnessRadix.TableNew.capacityTimes (localVar "stride"))] ++
    Arenas.Prefix.fieldActions "t" "unused" (pointerFields 32 "keys" 0#64) ++
  [.allocate "vals" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] ++
    Arenas.Prefix.fieldActions "t" "unused" (pointerFields 40 "vals" 0#64) ++
  [.allocate "used" (localVar "cap")]
def clearCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "used", localVar "cap"]
def finishActions : List Action := [.command clearCall] ++
    Arenas.Prefix.fieldActions "t" "unused" (pointerFields 48 "used" 0#64) ++
  [.allocate "order" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] ++
    Arenas.Prefix.fieldActions "t" "unused" (pointerFields 56 "order" 0#64) ++
  [.allocate "order_pos" (WitnessRadix.TableNew.capacityTimes (.const 8#64))] ++
    Arenas.Prefix.fieldActions "t" "unused" (pointerFields 64 "order_pos" 0#64)
def actions : List Action := firstActions ++ middleActions ++ finishActions

def body : ProgHOL 64 := match Guest.guestFn_htab_new_scratch with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = Arenas.Prefix.program .down actions WitnessRadix.TableNew.returnTable := by
  simp only [body, Guest.guestFn_htab_new_scratch, progToHOL, expToHOL, shapeToHOL, List.map_cons,
    List.map_nil, Option.map_none, actions, firstActions, middleActions, finishActions,
    List.cons_append, List.nil_append, Arenas.Prefix.program, Arenas.functionName,
    Arenas.Prefix.fieldActions, Arenas.Prefix.fieldCommands, headerFields, pointerFields,
    FieldStores.address, FieldStores.Value.expression, WitnessRadix.TableNew.headerStore,
    WitnessRadix.TableNew.capacityTimes, WitnessRadix.TableNew.stride, WitnessRadix.TableNew.returnTable,
    clearCall, localVar, addConst]

noncomputable def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (fields : List FieldStores.Field) :=
  {source with memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes (cursor scratch 72) fields)}
noncomputable def tableState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState source "t" (cursor scratch 72)
noncomputable def strideState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (tableState source scratch) "stride" 24#64
noncomputable def initialState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (strideState source scratch) scratch headerFields
noncomputable def keysState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState (initialState source scratch) "keys" (cursor scratch 168)
noncomputable def keysStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (keysState source scratch) scratch (pointerFields 32 "keys" (cursor scratch 168))
noncomputable def valsState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState (keysStored source scratch) "vals" (cursor scratch 200)
noncomputable def valsStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (valsState source scratch) scratch (pointerFields 40 "vals" (cursor scratch 200))
noncomputable def preClearState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState (valsStored source scratch) "used" (cursor scratch 208)
noncomputable def clearState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  {preClearState source scratch with
    memory := (WitnessRadix.Zero.memoryByte (preClearState source scratch).memory source.be (cursor scratch 208) 0 4)
    clock := (preClearState source scratch).clock - 5}
noncomputable def usedStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (clearState source scratch) scratch (pointerFields 48 "used" (cursor scratch 208))
noncomputable def orderState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState (usedStored source scratch) "order" (cursor scratch 240)
noncomputable def orderStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (orderState source scratch) scratch (pointerFields 56 "order" (cursor scratch 240))
noncomputable def positionState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  Arenas.Prefix.expectedState (orderStored source scratch) "order_pos" (cursor scratch 272)
noncomputable def finalState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  stored (positionState source scratch) scratch (pointerFields 64 "order_pos" (cursor scratch 272))

end InitECandidate.Solver.ScratchTable

#print axioms InitECandidate.Solver.ScratchTable.body_shape
