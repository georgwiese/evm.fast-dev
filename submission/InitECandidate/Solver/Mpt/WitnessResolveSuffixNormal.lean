import InitECandidate.Solver.Mpt.WitnessResolveControl
import InitECandidate.Solver.Mpt.WitnessResolveDatabaseNormal

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete normal-result classification for the original parsed
resolver suffix: empty, a genuine fresh hashed node, or a bounded next
decode slice. The same run supplies each nonlocal memory/heap frame. -/
theorem suffix_normal (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload flag heap : BitVec 64)
    (actual : Input.CurrentTable.NodeLookup.Database source data)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (small : length.toNat≤1024) (lower : 2701131776≤pointer.toNat) (before : pointer.toNat+length.toNat≤data.table.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (WitnessStep.afterRlp .resolve)=(some (.returned value),post)) :
    (value=.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)] ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase source) ∨
    (value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
      payload=32#64 ∧ heap.toNat+32≤2952790016 ∧ AllocatedBytes.Arena heap 32 ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase (hashAllocated source heap (pointer+header))) ∨
    ∃ nextPointer nextLength pending,
      value=.rStruct [.val (.word 1#64),.val (.word nextPointer),.val (.word nextLength),.val (.word pending)] ∧
      nextLength.toNat≤1024 ∧ 2701131776≤nextPointer.toNat ∧ nextPointer.toNat+nextLength.toNat≤data.table.toNat ∧
      (pending=0#64 ∨ pending=pointer+header ∧ payload=32#64) ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  rw [suffix_choice source pointer header payload flag itemCell] at normal
  by_cases string : flag=0#64
  · rw [if_pos string,string_choice source pointer header payload flag itemCell] at normal
    by_cases empty : payload=0#64
    · rw [if_pos empty] at normal
      obtain ⟨read,postEq⟩:=Input.return_normal source post _ value normal
      have expected : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=
          some (.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]):=rfl
      exact Or.inl ⟨Option.some.inj (read.symm.trans expected),by rw [postEq]; rfl⟩
    · rw [if_neg empty] at normal
      obtain ⟨thirtyTwo,continued⟩:=nonempty_normal source post pointer header payload flag itemCell installed value normal
      rcases lookup_normal data source post pointer header payload flag heap actual dbCell itemCell heapCell arena aligned installed value continued with hashed|found
      · obtain ⟨valueEq,room,nodeArena,frame⟩:=hashed
        exact Or.inr (Or.inl ⟨valueEq,thirtyTwo,room,nodeArena,frame⟩)
      · obtain ⟨nextPointer,nextLength,valueEq,small,sliceArena,lower,before,frame⟩:=found
        exact Or.inr (Or.inr ⟨nextPointer,nextLength,pointer+header,valueEq,small,lower,before,Or.inr ⟨rfl,thirtyTwo⟩,frame⟩)
  · rw [if_neg string] at normal
    obtain ⟨read,postEq⟩:=Input.return_normal source post _ value normal
    have expected : eval source (.rstruct [.const 1#64,localVar "p",localVar "n",.const 0#64])=
        some (.rStruct [.val (.word 1#64),.val (.word pointer),.val (.word length),.val (.word 0#64)]):=by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,pointerCell,lengthCell]
    exact Or.inr (Or.inr ⟨pointer,length,0#64,Option.some.inj (read.symm.trans expected),small,lower,before,Or.inl rfl,by rw [postEq]; rfl⟩)

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.suffix_normal
