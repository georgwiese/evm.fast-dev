import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.ByteStoreClock
import InitECandidate.Solver.WitnessRadix.ZeroByteStore

namespace InitECandidate.Solver.Input.ZeroByteFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def byteStore (offset : Nat) : ProgHOL 64 := .storeByte
  (.op .add (if offset=0 then [localVar "dst",localVar "i"] else [localVar "dst",localVar "i",.const (BitVec.ofNat 64 offset)])) (.const 0#64)
def stores (offsets : List Nat) (tail : ProgHOL 64) := offsets.foldr (fun offset rest=>.seq (byteStore offset) rest) tail

theorem byte_shape : Zero.byteBody=stores [0,1,2,3,4,5,6,7] (Zero.increment 8#64) := by
  simp only [Zero.byteBody,Zero.loopBytes,Zero.body,BuildProgram.loops,Guest.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,stores,List.foldr_cons,List.foldr_nil,byteStore,Zero.increment,localVar,addConst]
  rfl

theorem stores_summary (key : MlS) (offsets : List Nat) (tail : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key tail source) :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key (stores offsets tail) source := by
  induction offsets with
  | nil=>exact safe
  | cons offset rest ih=>
    intro source
    exact local_summary_sequence key (byteStore offset) (stores rest tail) (byte_store_local key _ _) ih source

theorem stores_advance (key : MlS) (offsets : List Nat) (tail : ProgHOL 64) (amount : Nat) (next : CounterFlow.Advances key amount tail) :
    CounterFlow.Advances key amount (stores offsets tail) := by
  induction offsets with
  | nil=>exact next
  | cons offset rest ih=>simpa only [Nat.zero_add,stores,List.foldr_cons] using (CounterFlow.sequence key (byteStore offset) (stores rest tail) 0 amount (CounterFlow.byte_store key _ _) ih)

theorem stores_quiet (code) (offsets : List Nat) (tail : ProgHOL 64) (quiet : QuietClock.Preserves code tail) : QuietClock.Preserves code (stores offsets tail) := by
  induction offsets with
  | nil=>exact quiet
  | cons offset rest ih=>exact QuietClock.sequence code _ _ (QuietClock.store_byte code _ _) ih

/-- Real original byte-loop blocks have zero source-clock body price and
advance their actual counter by8, with all other caller locals preserved. -/
theorem byte_quiet (code) : QuietClock.Preserves code Zero.byteBody := by
  rw [byte_shape]
  exact stores_quiet code _ _ (QuietClock.assign code _ _)

theorem byte_advance : CounterFlow.Advances (ofString "i") 8 Zero.byteBody := by
  rw [byte_shape]
  exact stores_advance (ofString "i") _ _ 8 (CounterFlow.increment_by (ofString "i") 8)

theorem byte_summary (key : MlS) (different : key≠ofString "i") : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key Zero.byteBody source := by
  rw [byte_shape]
  exact stores_summary key _ _ (LocalPrefix.assign _ _ different).summary_full

theorem tail_quiet (code) : QuietClock.Preserves code Zero.tailBody := by
  rw [Zero.tail_body_shape]
  exact QuietClock.sequence code _ _ (QuietClock.store_byte code _ _) (QuietClock.assign code _ _)

theorem tail_advance : CounterFlow.Advances (ofString "i") 1 Zero.tailBody := by
  rw [Zero.tail_body_shape]
  exact CounterFlow.sequence (ofString "i") _ _ 0 1 (CounterFlow.byte_store (ofString "i") _ _) (CounterFlow.increment_by (ofString "i") 1)

theorem tail_summary (key : MlS) (different : key≠ofString "i") : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,LocalSummary key Zero.tailBody source := by
  intro source
  rw [Zero.tail_body_shape]
  exact local_summary_sequence key _ _ (byte_store_local key _ _) (LocalPrefix.assign _ _ different).summary_full source

end InitECandidate.Solver.Input.ZeroByteFlow

#print axioms InitECandidate.Solver.Input.ZeroByteFlow.byte_shape
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.byte_quiet
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.byte_advance
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.byte_summary
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.tail_quiet
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.tail_advance
#print axioms InitECandidate.Solver.Input.ZeroByteFlow.tail_summary
