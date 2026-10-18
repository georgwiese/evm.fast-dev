import InitECandidate.Solver.MutableTable.CopyBudget
import InitECandidate.Solver.WitnessRadix.TableState

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stage_away (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (pool : Pool) (query : BitVec 64)
    (outside : ∀ other, query.toNat < next.base other ∨ next.base other + size kind next other ≤ query.toNat) :
    stageMemory input be kind old next pool query = input query := by
  have fits : amount kind old.capacity pool ≤ size kind next pool := by rw [← sameCapacity]; exact amount_room kind next pool
  have copyAway : CopyGeneral.Away (cell next pool 0) query (amount kind old.capacity pool) := by
    rw [← region_pointer kind next pool]
    exact MemoryRegion.copy_away _ (MemoryRegion.pool_valid kind next nextValid pool) _ fits query (outside pool)
  have copied := CopyGeneral.resultMemory_away input be (cell old pool 0) (cell next pool 0) query (amount kind old.capacity pool) copyAway
  unfold stageMemory
  split
  · exact copied
  · rw [StoreWord.put, if_neg]
    · exact copied
    · intro equal
      have numeric := congrArg BitVec.toNat equal
      have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
      rw [number kind next nextValid .header _ fieldInside] at numeric
      have other := outside .header
      change query.toNat < next.base .header ∨ next.base .header + 72 ≤ query.toNat at other
      change headerOffset pool < 72 at fieldInside
      omega

theorem walk_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (selected : List Pool) (query : BitVec 64)
    (outside : ∀ other, query.toNat < next.base other ∨ next.base other + size kind next other ≤ query.toNat) :
    (walk source kind old next selected).memory query = source.memory query := by
  induction selected generalizing source with
  | nil => rfl
  | cons pool rest ih =>
    rw [walk, ih, stage_memory]
    exact stage_away source.memory source.be kind old next nextValid sameCapacity pool query outside

def walkGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) (kind : KeyHash.Kind) (next : Plan) : List Pool → HolFiniteMapExact MlS (ValueHOL 64)
  | [] => globals
  | pool :: rest => walkGlobals (globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool))))) kind next rest

theorem walk_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (selected : List Pool) :
    emptyLocalsHOLFinite (walk source kind old next selected) = emptyLocalsHOLFinite {source with
      globals := walkGlobals source.globals kind next selected
      memory := (walk source kind old next selected).memory
      clock := source.clock - walkPrice kind old next selected} := by
  induction selected generalizing source with
  | nil => simp only [walk, walkGlobals, walkPrice, Nat.sub_zero]
  | cons pool rest ih =>
    rw [walk, ih]
    have firstFrame := stage_frame source kind old next pool
    have globalsEq := congrArg (fun state : PanSemStateFiniteExact 64 F => state.globals) firstFrame
    change (stageState source kind old next pool).globals = source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool)))) at globalsEq
    have clockEq := stage_clock source kind old next pool
    rw [globalsEq, clockEq]
    have subtraction : source.clock - stagePrice kind old next pool - walkPrice kind old next rest = source.clock - walkPrice kind old next (pool :: rest) := by
      change source.clock - stagePrice kind old next pool - walkPrice kind old next rest = source.clock - (stagePrice kind old next pool + walkPrice kind old next rest)
      omega
    rw [subtraction]
    have overwritten := congrArg (fun state : PanSemStateFiniteExact 64 F => emptyLocalsHOLFinite {state with
      globals := walkGlobals source.globals kind next (pool :: rest)
      memory := (walk (stageState source kind old next pool) kind old next rest).memory
      clock := source.clock - walkPrice kind old next (pool :: rest)}) firstFrame
    exact overwritten

def changed {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan) (start paid : Nat) (memory : WordWrites.Memory) :=
  {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start old.capacity))))
    memory := memory
    clock := source.clock - paid}

theorem final_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old : Plan) (start : Nat) :
    emptyLocalsHOLFinite (finalState source kind old start) = emptyLocalsHOLFinite
      (changed source kind old start (walkPrice kind old (fresh kind start old.capacity) pools) (finalState source kind old start).memory) := by
  rw [finalState, walk_frame]
  simp only [walkGlobals, pools, changed, initial, WitnessRadix.QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite,
    TableNew.update_twice, fresh, size, freshEnd]

theorem final_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start : Nat)
    (nextValid : Valid kind (fresh kind start old.capacity)) (query : BitVec 64)
    (outside : query.toNat < start ∨ freshEnd kind start old.capacity ≤ query.toNat) :
    (finalState source kind old start).memory query = source.memory query := by
  apply walk_away _ kind old _ nextValid rfl pools query
  intro pool
  cases pool <;> simp only [fresh, size] <;> dsimp only [freshEnd] at outside <;> omega

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_away
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_away
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_frame
#print axioms InitECandidate.Solver.MutableTable.TableCopy.final_frame
#print axioms InitECandidate.Solver.MutableTable.TableCopy.final_away
