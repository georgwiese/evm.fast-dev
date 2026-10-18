import InitECandidate.Solver.MutableTable.CopyStageExecution

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def walk {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) : List Pool → PanSemStateFiniteExact 64 F
  | [] => source
  | pool :: rest => walk (stageState source kind old next pool) kind old next rest
def walkPrice (kind : KeyHash.Kind) (old next : Plan) : List Pool → Nat
  | [] => 0
  | pool :: rest => stagePrice kind old next pool + walkPrice kind old next rest
def cursor (next : Plan) (ending : Nat) : List Pool → Nat
  | [] => ending
  | pool :: _ => next.base pool
def Chain (kind : KeyHash.Kind) (next : Plan) (ending : Nat) : List Pool → Prop
  | [] => True
  | pool :: rest => next.base pool + size kind next pool = cursor next ending rest ∧ Chain kind next ending rest

theorem walk_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (selected : List Pool) :
    (walk source kind old next selected).clock = source.clock - walkPrice kind old next selected := by
  induction selected generalizing source with
  | nil => simp only [walk, walkPrice, Nat.sub_zero]
  | cons pool rest ih => rw [walk, ih, stage_clock, walkPrice]; omega

theorem walk_preserves_old (input : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second) (selected : List Pool) :
    MemoryModel.PoolFrame input.memory (walk input kind old next selected).memory kind old := by
  induction selected generalizing input with
  | nil => exact MemoryModel.PoolFrame.refl _ _ _
  | cons pool rest ih =>
    apply MemoryModel.PoolFrame.trans input.memory (stageState input kind old next pool).memory _ kind old
    · rw [stage_memory]
      exact stage_preserves_old _ _ kind old next oldValid nextValid sameCapacity earlier pool
    · exact ih _

/-- The full original ordered copy stages compose actual allocations,
copies, stores and declaration scopes. Entry code/heap/room/clock and old
table ownership are explicit; successful helper runs are derived. -/
theorem walk_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (selected : List Pool) (ending : Nat) (chain : Chain kind next ending selected)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64) (header : MemoryModel.Header source.memory kind old count)
    (locals : CoreLocals source kind old)
    (newHeader : selected.head? ≠ some .header → source.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor next ending selected)))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : walkPrice kind old next selected ≤ source.clock) :
    ∃ restoreStack, Executes source (selected.flatMap stageActions) (walk source kind old next selected) restoreStack := by
  induction selected generalizing source with
  | nil => exact ⟨id, .done _⟩
  | cons pool rest ih =>
    have firstFunded : stagePrice kind old next pool ≤ source.clock := by change stagePrice kind old next pool + _ ≤ source.clock at enough; omega
    have nReady : pool ≠ .header → source.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))) := by
      intro different
      exact newHeader (by simpa only [List.head?_cons, ne_eq, Option.some.injEq] using different)
    obtain ⟨restoreFirst, firstRun⟩ := stage_executes source kind old next oldValid nextValid sameCapacity domain count header locals pool nReady heap allocCode copyCode firstFunded
    let post := stageState source kind old next pool
    have frame := stage_frame source kind old next pool
    have domainKept := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
    have codeKept := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) frame
    have heapSet := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
    have nextDomain : post.memaddrs = InitE.ordinaryDomain := domainKept.trans domain
    have nextAlloc : post.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one) := by rw [show post.code = source.code from codeKept]; exact allocCode
    have nextCopy : post.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one) := by rw [show post.code = source.code from codeKept]; exact copyCode
    have nextHeader : MemoryModel.Header post.memory kind old count := by
      apply MemoryModel.Header.of_pool_frame source.memory post.memory kind old count header
      rw [show post.memory = stageMemory source.memory source.be kind old next pool from stage_memory source kind old next pool]
      exact stage_preserves_old _ _ kind old next oldValid nextValid sameCapacity earlier pool
    have nextHeap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor next ending rest)))) := by
      rw [show post.globals = source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool)))) from heapSet]
      rw [chain.1]
      simp [HolFiniteMapExact.update, FUPDATE]
    have nextFunded : walkPrice kind old next rest ≤ post.clock := by
      rw [show post.clock = source.clock - stagePrice kind old next pool from stage_clock source kind old next pool]
      change stagePrice kind old next pool + _ ≤ source.clock at enough
      omega
    obtain ⟨restoreRest, restRun⟩ := ih post chain.2 nextDomain nextHeader (CoreLocals.stage source kind old next pool locals)
      (by intro _; exact stage_new_header source kind old next pool nReady) nextHeap nextAlloc nextCopy nextFunded
    exact ⟨fun target => restoreFirst (restoreRest target), executes_append firstRun restRun⟩

theorem fresh_chain (kind : KeyHash.Kind) (start capacity : Nat) :
    Chain kind (fresh kind start capacity) (freshEnd kind start capacity) pools := by
  simp only [Chain, pools, cursor, fresh, freshEnd, size, and_true]

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_clock
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_preserves_old
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_executes
#print axioms InitECandidate.Solver.MutableTable.TableCopy.fresh_chain
