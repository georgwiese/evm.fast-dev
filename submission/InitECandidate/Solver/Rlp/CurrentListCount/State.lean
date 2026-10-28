import InitECandidate.Solver.Rlp.ListCountSyntax
import InitECandidate.Solver.Rlp.CurrentItemTotalCall

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- The current real list counter, with original input extent and initialized
arenas. Count cannot exceed already consumed bytes; no mapped scratch is used. -/
structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length offset count : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))
  countCell : source.locals.lookup (ofString "count")=some (.val (.word count))
  counted : count.toNat≤offset.toNat
  bounded : offset.toNat≤length.toNat
  fits : pointer.toNat+length.toNat<2^64

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length offset count : BitVec 64}

theorem View.at_clock (data : View source pointer length offset count) (clock : Nat) :
    View {source with clock:=clock} pointer length offset count :=
  ⟨data.arena.of_frame rfl,data.pointerCell,data.lengthCell,data.offsetCell,data.countCell,data.counted,data.bounded,data.fits⟩

theorem View.bound (data : View source pointer length offset count) (name : String) (word : BitVec 64)
    (different : ofString name≠ofString "p" ∧ ofString name≠ofString "len" ∧ ofString name≠ofString "off" ∧ ofString name≠ofString "count") :
    View (bind source name word) pointer length offset count :=
  ⟨data.arena.of_frame rfl,(bind_lookup_other source name "p" word different.1).trans data.pointerCell,
    (bind_lookup_other source name "len" word different.2.1).trans data.lengthCell,
    (bind_lookup_other source name "off" word different.2.2.1).trans data.offsetCell,
    (bind_lookup_other source name "count" word different.2.2.2).trans data.countCell,data.counted,data.bounded,data.fits⟩

theorem View.restored (data : View source pointer length offset count) (saved : PanSemStateFiniteExact 64 Guest.HostMemory) :
    View (restore saved "total" source) pointer length offset count :=
  ⟨data.arena.of_frame rfl,(restore_lookup_other saved source "total" "p" (by decide)).trans data.pointerCell,
    (restore_lookup_other saved source "total" "len" (by decide)).trans data.lengthCell,
    (restore_lookup_other saved source "total" "off" (by decide)).trans data.offsetCell,
    (restore_lookup_other saved source "total" "count" (by decide)).trans data.countCell,data.counted,data.bounded,data.fits⟩

def Invariant (pointer length : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop := ∃ offset count,View source pointer length offset count
def allowance (length : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  46*(length.toNat-(CurrentValidation.wordAt source "off").toNat)

theorem View.allowance_eq (data : View source pointer length offset count) : allowance length source=46*(length.toNat-offset.toNat) := by
  simp only [allowance,CurrentValidation.wordAt,data.offsetCell]

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.View.at_clock
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.View.bound
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.View.restored
