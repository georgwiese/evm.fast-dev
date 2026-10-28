import InitECandidate.Solver.Input.CurrentTable.Set.Program
import InitECandidate.Solver.Input.LocalWord

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

/-- The insertion search uses its actual d/p locals, rather than the
separate find-leaf function's keybits local. -/
structure SeekState (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base node parent pointer : BitVec 64) (difference : Nat) : Prop where
  cursor : Cursor origin source base node
  parentCell : source.locals.lookup (ofString "p") = some (.val (.word parent))
  differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference)))
  keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer))

theorem SeekState.with_bit {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference : Nat}
    (ready : SeekState origin source base node parent pointer difference) (word : BitVec 64) :
    SeekState origin (bind source "b" word) base node parent pointer difference :=
  ⟨ready.cursor.with_local "b" word (by decide) (by decide),
    (bind_lookup_other source "b" "p" word (by decide)).trans ready.parentCell,
    (bind_lookup_other source "b" "d" word (by decide)).trans ready.differenceCell,
    (bind_lookup_other source "b" "key" word (by decide)).trans ready.keyCell⟩

theorem SeekState.at_tick {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference : Nat}
    (ready : SeekState origin source base node parent pointer difference) :
    SeekState origin (decClockHOLFinite source) base node parent pointer difference :=
  ⟨ready.cursor.at_tick,ready.parentCell,ready.differenceCell,ready.keyCell⟩

theorem stop_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bit difference : Nat)
    (bitBound : bit ≤ 256) (differenceBound : difference ≤ 256)
    (bitCell : source.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 bit))))
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference)))) :
    eval source (.cmp .notLower (localVar "b") (localVar "d")) =
      some (.val (.word (if difference ≤ bit then 1#64 else 0#64))) := by
  have bitNumber : (BitVec.ofNat 64 bit).toNat = bit := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have differenceNumber : (BitVec.ofNat 64 difference).toNat = difference := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases stopped : difference ≤ bit
  · have inactive : ¬bit < difference := by omega
    simp [eval,evalHOLExact,localVar,bitCell,differenceCell,wordCmpHOL,BitVec.lt_def,bitNumber,differenceNumber,stopped,inactive]
  · have active : bit < difference := by omega
    simp [eval,evalHOLExact,localVar,bitCell,differenceCell,wordCmpHOL,BitVec.lt_def,bitNumber,differenceNumber,stopped,active]

/-- The actual insertion body breaks at b≥d. Otherwise it sets its real
parent and chooses the same query-directed child as the earlier lookup. -/
theorem after_bit_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference : Nat}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : FindLeaf.Nodes origin base valid bits left right)
    (ready : SeekState origin source base node parent pointer difference)
    (member : valid node) (differenceBound : difference ≤ 256) (query : KeyBits.Key)
    (bitCell : source.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 (bits node)))))
    (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source afterBit =
      if difference ≤ bits node then (some .break,source) else
        (none,bind (bind source "p" node) "n" (if KeyBits.bit query (bits node) then right node else left node)) := by
  have testRead := stop_read source (bits node) difference (image.bitBound node member) differenceBound bitCell ready.differenceCell
  simp only [eval] at testRead
  rw [seek_shapes.2.2.2,stopGuard,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,testRead]
  by_cases stopped : difference ≤ bits node
  · simp [stopped,evaluateHOLFiniteState_break]
  · have internal : bits node < 256 := by omega
    simp only [if_neg stopped,if_pos (show (0#64 : BitVec 64) = 0 from rfl),evaluateHOLFiniteState_skip]
    have parentRun := StateSteps.assign_execute source "p" (localVar "n") parent node ready.parentCell
      (Request.local_word source "n" node ready.cursor.nodeCell)
    have nextCursor := ready.cursor.with_local "p" node (by decide) (by decide)
    have branchRun := FindLeaf.branch_execute image nextCursor member internal pointer query
      ((bind_lookup_other source "p" "key" node (by decide)).trans ready.keyCell)
      ((bind_lookup_other source "p" "b" node (by decide)).trans bitCell) (view.of_frame rfl)
    rw [setParent,evaluateHOLFiniteState_seq_line780,parentRun]
    exact branchRun

/-- The real insertion step restores b while retaining its new parent and
node; clock0 is permitted because this straight-line body spends no tick. -/
theorem step_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference : Nat}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : FindLeaf.Nodes origin base valid bits left right)
    (ready : SeekState origin source base node parent pointer difference)
    (member : valid node) (differenceBound : difference ≤ 256) (query : KeyBits.Key)
    (view : FirstDiff.ByteView source pointer query) :
    evaluateHOLFiniteState source seekStep =
      if difference ≤ bits node then (some .break,source) else
        (none,bind (bind source "p" node) "n" (if KeyBits.bit query (bits node) then right node else left node)) := by
  let entered := bind source "b" (BitVec.ofNat 64 (bits node))
  have state := ready.with_bit (BitVec.ofNat 64 (bits node))
  have read : eval source (.load .one (FindLeaf.address 24)) = some (.val (.word (BitVec.ofNat 64 (bits node)))) := by
    have domain := congrArg PanSemStateFiniteExact.memaddrs ready.cursor.frame
    change source.memaddrs = origin.memaddrs at domain
    have memory := LocalEffects.memory_of_erase origin source ready.cursor.frame
    exact Witness.load_word_read source _ _ _
      (FindLeaf.address_read source base node 24 ready.cursor.baseCell ready.cursor.nodeCell)
      (by rw [domain]; exact image.bitMapped node member) (by rw [memory]; exact image.bitCell node member)
  have afterRun := after_bit_execute image state member differenceBound query (bind_lookup_same _ _ _) (view.of_frame rfl)
  rw [seek_shapes.2.2.1]
  by_cases stopped : difference ≤ bits node
  · rw [if_pos stopped] at afterRun ⊢
    have actual := ScalarScope.declare_execute source entered "b" _ _ afterBit (some .break) read afterRun
    rw [actual,restore_bound]
  · rw [if_neg stopped] at afterRun ⊢
    let child := if KeyBits.bit query (bits node) then right node else left node
    have actual := ScalarScope.declare_execute source (bind (bind entered "p" node) "n" child) "b" _ _ afterBit none read afterRun
    rw [actual,restore_bind_other source (bind entered "p" node) "b" "n" child (by decide),
      restore_bind_other source entered "b" "p" node (by decide),restore_bound]

theorem step_quiet (code) : QuietClock.Preserves code seekStep := by
  rw [seek_shapes.2.2.1,seek_shapes.2.2.2,stopGuard,setParent]
  exact QuietClock.declared code _ _ _ _ (QuietClock.sequence code _ _
    (QuietClock.conditional code _ _ _ (QuietClock.stopped code).1 (QuietClock.skip code))
    (QuietClock.sequence code _ _ (QuietClock.assign code _ _)
      (by rw [FindLeaf.shapes.2.2.2]; exact QuietClock.conditional code _ _ _ (QuietClock.assign code _ _) (QuietClock.assign code _ _))))

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.after_bit_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.step_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.step_quiet
