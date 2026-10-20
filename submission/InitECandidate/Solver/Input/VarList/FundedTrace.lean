import InitECandidate.Solver.Input.VarList.BodyNormal

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual variable-list outcome, including malformed headers and record
ranges. A funded execution either returns or raises precisely SszErr20..23;
all its real loops and allocation cost at most length/4+2 source ticks. -/
theorem body_trace_funded (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (arrayRoom : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : length/4+2≤source.clock)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body = (result,post)) :
    source.clock - post.clock ≤ length/4+2 ∧
      ((∃ value,result = some (.returned value)) ∨ ∃ error : BitVec 64,
        (error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) := by
  classical
  rw [entry_execute source input pointer start length heap inside p n failCode exceptionShape (by omega)] at run
  by_cases empty : length=0
  · simp only [if_pos empty] at run
    have clock := congrArg (fun output => output.2.clock) run
    have answer := congrArg Prod.fst run
    exact ⟨by change source.clock = post.clock at clock; omega,Or.inl ⟨emptyValue,answer.symm⟩⟩
  simp only [if_neg empty] at run
  by_cases short : length<4
  · simp only [if_pos short] at run
    have clock := congrArg (fun output => output.2.clock) run
    have answer := congrArg Prod.fst run
    exact ⟨by change source.clock-1 = post.clock at clock; omega,Or.inr ⟨20#64,Or.inl rfl,answer.symm⟩⟩
  simp only [if_neg short] at run
  let first := BitVec.ofNat 64 (Guest.GasLimit.le32 input start)
  let entered := bind source "first" first
  have savedN : entered.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "first" "len" first (by decide)).trans n
  have savedL : entered.locals.lookup (ofString "lim") = some (.val (.word limit)) :=
    (bind_lookup_other source "first" "lim" first (by decide)).trans l
  have guards := first_guards entered first (BitVec.ofNat 64 length) limit (bind_lookup_same _ _ _) savedN savedL failCode exceptionShape (by change 1≤source.clock; omega)
  change (let output := evaluateHOLFiniteState entered firstTail; (output.1,restore source "first" output.2)) = (result,post) at run
  rw [guards] at run
  by_cases bad : badFirst first (BitVec.ofNat 64 length)
  · simp only [if_pos bad] at run
    have clock := congrArg (fun output => output.2.clock) run
    have answer := congrArg Prod.fst run
    exact ⟨by change source.clock-1 = post.clock at clock; omega,Or.inr ⟨21#64,Or.inr (Or.inl rfl),answer.symm⟩⟩
  simp only [if_neg bad] at run
  by_cases over : limit<countWord first
  · simp only [if_pos over] at run
    have clock := congrArg (fun output => output.2.clock) run
    have answer := congrArg Prod.fst run
    exact ⟨by change source.clock-1 = post.clock at clock; omega,Or.inr ⟨22#64,Or.inr (Or.inr (Or.inl rfl)),answer.symm⟩⟩
  simp only [if_neg over] at run
  obtain ⟨positive,header,firstUpper⟩ := first_valid first (BitVec.ofNat 64 length) bad
  have firstNat : first.toNat = Guest.GasLimit.le32 input start := RawScalar.le32_number input start
  have small : length<2^64 := by have := Nat.mod_lt input.length (show 0<2^64 by decide); omega
  have lengthNat : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  rw [count_number,firstNat] at positive header
  rw [firstNat,lengthNat] at firstUpper
  let plan : Plan input := {
    inputPointer:=pointer, array:=array, start:=start, length:=length, count:=Guest.GasLimit.le32 input start/4,
    positive:=positive, header:=by omega, slice:=inside, inputLower:=lower, inputAligned:=aligned,
    arrayAligned:=arrayAligned, arrayAfter:=arrayAfter, arrayRoom:=by omega }
  let ready:=counted entered first
  have firstHeap : Blob.HeapInput entered input pointer := Blob.HeapInput.bind source input pointer "first" first heap
  have readyHeap : Blob.HeapInput ready input plan.inputPointer := Blob.HeapInput.bind entered input pointer "count" (countWord first) firstHeap
  have rp : ready.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start))) :=
    (bind_lookup_other entered "count" "p" _ (by decide)).trans ((bind_lookup_other source "first" "p" first (by decide)).trans p)
  have rf : ready.locals.lookup (ofString "first")=some (.val (.word first)) :=
    (bind_lookup_other entered "count" "first" _ (by decide)).trans (bind_lookup_same _ _ _)
  have rn : ready.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other entered "count" "len" _ (by decide)).trans ((bind_lookup_other source "first" "len" first (by decide)).trans n)
  have rc : ready.locals.lookup (ofString "count")=some (.val (.word (BitVec.ofNat 64 plan.count))) := by
    have encoded : countWord first=BitVec.ofNat 64 plan.count := count_encode input start
    exact (bind_lookup_same entered "count" (countWord first)).trans
      (congrArg (fun word : BitVec 64=>some (ValueHOL.val (HolWordLab.word word))) encoded)
  have countBound : plan.count≤length/4 := by change Guest.GasLimit.le32 input start/4≤length/4; omega
  obtain ⟨computedResult,target,paid,computed,bound,clock,control,heapAfter,arrayFrame,outcome⟩:=allocation_execute ready input plan first (BitVec.ofNat 64 length) readyHeap domain
    rp rf rn rc failCode exceptionShape heapGlobal allocCode (by change plan.count+2≤source.clock; omega)
  change (let output := evaluateHOLFiniteState ready allocationCall;
    (output.1,restore source "first" (restore entered "count" output.2))) = (result,post) at run
  rw [computed] at run
  have answer := congrArg Prod.fst run
  have finalClock := congrArg (fun output => output.2.clock) run
  change target.clock = post.clock at finalClock
  change target.clock = source.clock-paid at clock
  have cost : source.clock-post.clock ≤ length/4+2 := by
    rw [← finalClock,clock]
    change paid≤Guest.GasLimit.le32 input start/4+2 at bound
    omega
  refine ⟨cost,?_⟩
  rcases outcome with normal | fault
  · exact Or.inl ⟨pairValue plan.array plan.count,answer.symm.trans normal.1⟩
  · exact Or.inr ⟨23#64,Or.inr (Or.inr (Or.inr rfl)),answer.symm.trans fault⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.body_trace_funded
