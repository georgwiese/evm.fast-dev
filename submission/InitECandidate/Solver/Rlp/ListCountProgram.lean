import InitECandidate.Solver.Rlp.ListCountSyntax
import InitECandidate.Solver.Rlp.ItemTotalCall

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64) : Prop where
  arena : Validation.Arena source cursor limit
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset))
  countCell : source.locals.lookup (ofString "count")=some (.val (.word count))
  counted : count.toNat≤offset.toNat
  bounded : offset.toNat≤length.toNat
  fits : pointer.toNat+length.toNat<2^64

theorem View.clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit offset count : BitVec 64)
    (view : View source pointer length cursor limit offset count) (clock : Nat) :
    View {source with clock:=clock} pointer length cursor limit offset count :=
  ⟨Validation.Arena.of_fields source _ cursor limit view.arena rfl rfl,view.pointerCell,view.lengthCell,view.offsetCell,view.countCell,view.counted,view.bounded,view.fits⟩

def Invariant (pointer length cursor limit : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ offset count,View source pointer length cursor limit offset count
def allowance (length : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  60*(length.toNat-(Validation.localWord source "off").toNat)+31

theorem allowance_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length offset : BitVec 64)
    (cell : source.locals.lookup (ofString "off")=some (.val (.word offset))) :
    allowance length source=60*(length.toNat-offset.toNat)+31 := by simp only [allowance,Validation.localWord,cell]

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.View.clock
#print axioms InitECandidate.Solver.Rlp.ListCount.allowance_eq
