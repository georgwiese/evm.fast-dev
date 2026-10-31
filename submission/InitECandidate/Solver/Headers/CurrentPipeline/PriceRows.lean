import InitECandidate.Solver.Headers.CurrentPipeline.Price

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack PanSemStateFiniteExact

private theorem range23 : List.range 23=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] := by decide

/-- Collect the exact finite pipeline: every row is decoded at most
twice, and all helper/caller fixed overhead sums to at most455. -/
theorem price_rows (items : List Rlp.ListItem) (current : BitVec 64) :
    price items current fields≤120*((List.range 23).map (rowBytes items)).sum+455 := by
  by_cases zero : current=0#64
  all_goals
    simp only [price,fields,afterF,afterD,afterW,afterTsf,afterEx,afterBg,final,bytesSet,wordSet,u256Set,uintSet,
      CurrentHelpers.bodyPrice,CurrentHelpers.overhead,range23,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  · rw [if_pos zero]
    omega
  · rw [if_neg zero]
    omega

/-- Padding the real list to the largest original header count contributes
zero for absent rows, without inventing mapped sentinel entries. -/
theorem row_sum (items : List Rlp.ListItem) (count : Nat) (fits : items.length≤count) :
    ((List.range count).map (rowBytes items)).sum=(items.map fun item=>item.total.toNat).sum := by
  induction count generalizing items with
  | zero=>
    have empty : items=[] := List.length_eq_zero_iff.mp (by omega)
    subst items
    rfl
  | succ count ih=>
    cases items with
    | nil=>
      change ((List.range (count+1)).map (fun index=>rowBytes [] index)).sum=0
      simp [rowBytes]
    | cons head tail=>
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.sum_cons,List.map_map]
      change head.total.toNat+((List.range count).map (rowBytes tail)).sum=head.total.toNat+(tail.map fun item=>item.total.toNat).sum
      rw [ih tail (by simp only [List.length_cons] at fits; omega)]

theorem encoded_sum (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (model : Rlp.ListItems source pointer bytes items) : (items.map fun item=>item.total.toNat).sum≤bytes := by
  induction model with
  | nil=>simp
  | cons pointer item bytes items encoded valid rest ih=>
    have reduced : item.total.toNat≤item.size := by
      change (item.header.toNat+item.payload.toNat)%2^64≤item.header.toNat+item.payload.toNat
      exact Nat.mod_le _ _
    simp only [List.map_cons,List.sum_cons]
    omega

theorem price_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (current : BitVec 64) (model : Rlp.ListItems source pointer bytes items) (count : items.length≤23) :
    price items current fields≤120*bytes+455 := by
  have rows:=price_rows items current
  rw [row_sum items 23 count] at rows
  have total:=encoded_sum source pointer bytes items model
  omega

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.price_rows
#print axioms InitECandidate.Solver.Headers.CurrentPipeline.price_bytes
