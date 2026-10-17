import InitECandidate.Solver.Input.VarList.NormalSummary

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Concrete initialized record-array evidence on every normal decoder result.
Empty slices impose no positive pointer or readable-record requirement. -/
def Records (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) : Prop :=
  length=0 ∨ ∃ plan : Plan input,
    plan.inputPointer=pointer ∧ plan.array=array ∧ plan.start=start ∧ plan.length=length ∧
    plan.count=Guest.GasLimit.le32 input start/4 ∧ Complete source input plan (BitVec.ofNat 64 length) ∧
    ∀ position,position<plan.count→Offsets.ValidAt (BitVec.ofNat 64 (Guest.GasLimit.le32 input start))
      (BitVec.ofNat 64 length) (currentWord input start) position

theorem Records.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat) (memory : target.memory=source.memory)
    (records : Records source input pointer array start length) : Records target input pointer array start length := by
  rcases records with empty|nonempty
  · exact Or.inl empty
  · obtain ⟨plan,p,a,s,n,c,complete,valid⟩:=nonempty
    refine Or.inr ⟨plan,p,a,s,n,c,?_,valid⟩
    intro position inside
    change _ ∧ _
    rw [memory]
    exact complete position inside

theorem normal_records (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : length/4+2≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Records post input pointer array start length := by
  classical
  by_cases empty : length=0
  · exact Or.inl empty
  · have positive : 0<length := by omega
    have parsed:=normal_entry source post input pointer limit start length heap inside p n l failCode exceptionShape (by omega) value run
    have countBound : Guest.GasLimit.le32 input start/4≤length/4 := by
      rcases parsed with nil|list
      · omega
      · obtain ⟨minimum,countPositive,header,firstUpper,limitUpper,rest⟩:=list
        omega
    obtain ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,valueEq,clockEq,control,postHeap,frame,complete,valid⟩:=
      nonempty_normal source post input pointer array limit start length positive heap inside p n l domain lower aligned arrayAligned arrayAfter
        (by omega) heapGlobal allocCode failCode exceptionShape enough value run
    exact Or.inr ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.Records.of_memory
#print axioms InitECandidate.Solver.Input.VarList.normal_records
