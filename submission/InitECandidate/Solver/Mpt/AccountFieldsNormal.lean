import InitECandidate.Solver.Mpt.AccountFieldNormal
import InitECandidate.Solver.Mpt.AccountFieldsCost

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Four actual current decoder results, each referring to its selected
physical input span. Their headers/payloads are derived by real calls. -/
structure FieldResults (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (a b c d : Rlp.ListItem) where
  value0 : ValueHOL 64
  value1 : ValueHOL 64
  value2 : ValueHOL 64
  value3 : ValueHOL 64
  cell0 : source.locals.lookup (ofString "f0")=some value0
  cell1 : source.locals.lookup (ofString "f1")=some value1
  cell2 : source.locals.lookup (ofString "f2")=some value2
  cell3 : source.locals.lookup (ofString "f3")=some value3
  valid0 : Rlp.Item.Valid (Rlp.Slices.itemPointer pointer [a,b,c,d] 0) a.total.toNat value0
  valid1 : Rlp.Item.Valid (Rlp.Slices.itemPointer pointer [a,b,c,d] 1) b.total.toNat value1
  valid2 : Rlp.Item.Valid (Rlp.Slices.itemPointer pointer [a,b,c,d] 2) c.total.toNat value2
  valid3 : Rlp.Item.Valid (Rlp.Slices.itemPointer pointer [a,b,c,d] 3) d.total.toNat value3
  exact0 : value0=Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 0) a.header a.payload a.flag
  exact1 : value1=Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 1) b.header b.payload b.flag
  exact2 : value2=Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 2) c.header c.payload c.flag
  exact3 : value3=Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 3) d.header d.payload d.flag

set_option maxRecDepth 10000 in
/-- All four genuine original calls reach afterFields with their real
current tuples. Their scratch frames compose, retaining the complete
physical records/input view and unchanged heap/domain/endian/code. -/
theorem fields_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length cursor limit out : BitVec 64) (cutoff : Nat) (a b c d : Rlp.ListItem)
    (view : FieldsView source array pointer length cursor limit out cutoff [a,b,c,d])
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source fields=(some (.returned returned),post)) :
    ∃ ready inner,Nonempty (FieldResults ready pointer a b c d) ∧
      FieldsView ready array pointer length cursor limit out cutoff [a,b,c,d] ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      ready.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      evaluateHOLFiniteState ready afterFields=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  rw [fields_shape] at normal
  change evaluateHOLFiniteState source (.decCall (ofString "f0") Rlp.Item.resultShape (ofString "rlp_item") (fieldArguments 0) lastThree)=(some (.returned returned),post) at normal
  obtain ⟨post0,h0,p0,f0,inner0,valid0,match0,view0,above0,domain0,endian0,code0,heap0,price0,run0,restore0⟩ :=
    field_normal source post array pointer length cursor limit out cutoff [a,b,c,d] 0 a "f0" lastThree view rfl (by decide) (by decide) installed returned normal
  let value0 := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 0) h0 p0 f0
  let ready0 := Input.CallNormal.continuationEntry source post0 "f0" value0
  have installed0 : Input.OriginalCode.Installed ready0.code := by change Input.OriginalCode.Installed post0.code; rw [code0]; exact installed
  obtain ⟨post1,h1,p1,f1,inner1,valid1,match1,view1,above1,domain1,endian1,code1,heap1,price1,run1,restore1⟩ :=
    field_normal ready0 inner0 array pointer length cursor limit out cutoff [a,b,c,d] 1 b "f1" lastTwo view0 rfl (by decide) (by decide) installed0 returned run0
  let value1 := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 1) h1 p1 f1
  let ready1 := Input.CallNormal.continuationEntry ready0 post1 "f1" value1
  have installed1 : Input.OriginalCode.Installed ready1.code := by change Input.OriginalCode.Installed post1.code; rw [code1]; exact installed0
  obtain ⟨post2,h2,p2,f2,inner2,valid2,match2,view2,above2,domain2,endian2,code2,heap2,price2,run2,restore2⟩ :=
    field_normal ready1 inner1 array pointer length cursor limit out cutoff [a,b,c,d] 2 c "f2" lastField view1 rfl (by decide) (by decide) installed1 returned run1
  let value2 := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 2) h2 p2 f2
  let ready2 := Input.CallNormal.continuationEntry ready1 post2 "f2" value2
  have installed2 : Input.OriginalCode.Installed ready2.code := by change Input.OriginalCode.Installed post2.code; rw [code2]; exact installed1
  obtain ⟨post3,h3,p3,f3,inner3,valid3,match3,view3,above3,domain3,endian3,code3,heap3,price3,run3,restore3⟩ :=
    field_normal ready2 inner2 array pointer length cursor limit out cutoff [a,b,c,d] 3 d "f3" afterFields view2 rfl (by decide) (by decide) installed2 returned run2
  let value3 := Rlp.Item.result (Rlp.Slices.itemPointer pointer [a,b,c,d] 3) h3 p3 f3
  let ready3 := Input.CallNormal.continuationEntry ready2 post3 "f3" value3
  have cell00 : ready0.locals.lookup (ofString "f0")=some value0 := Input.CallNormal.continuation_lookup_same _ _ _ _
  have cell01 : ready1.locals.lookup (ofString "f0")=some value0 :=
    (Input.CallNormal.continuation_lookup_other ready0 post1 "f1" "f0" value1 (by decide)).trans cell00
  have cell02 : ready2.locals.lookup (ofString "f0")=some value0 :=
    (Input.CallNormal.continuation_lookup_other ready1 post2 "f2" "f0" value2 (by decide)).trans cell01
  have cell03 : ready3.locals.lookup (ofString "f0")=some value0 :=
    (Input.CallNormal.continuation_lookup_other ready2 post3 "f3" "f0" value3 (by decide)).trans cell02
  have cell11 : ready1.locals.lookup (ofString "f1")=some value1 := Input.CallNormal.continuation_lookup_same _ _ _ _
  have cell12 : ready2.locals.lookup (ofString "f1")=some value1 :=
    (Input.CallNormal.continuation_lookup_other ready1 post2 "f2" "f1" value2 (by decide)).trans cell11
  have cell13 : ready3.locals.lookup (ofString "f1")=some value1 :=
    (Input.CallNormal.continuation_lookup_other ready2 post3 "f3" "f1" value3 (by decide)).trans cell12
  have cell22 : ready2.locals.lookup (ofString "f2")=some value2 := Input.CallNormal.continuation_lookup_same _ _ _ _
  have cell23 : ready3.locals.lookup (ofString "f2")=some value2 :=
    (Input.CallNormal.continuation_lookup_other ready2 post3 "f3" "f2" value3 (by decide)).trans cell22
  have cell33 : ready3.locals.lookup (ofString "f3")=some value3 := Input.CallNormal.continuation_lookup_same _ _ _ _
  have results : FieldResults ready3 pointer a b c d :=
    ⟨value0,value1,value2,value3,cell03,cell13,cell23,cell33,valid0,valid1,valid2,valid3,
      by simp only [value0,match0.1,match0.2.1,match0.2.2],by simp only [value1,match1.1,match1.2.1,match1.2.2],
      by simp only [value2,match2.1,match2.2.1,match2.2.2],by simp only [value3,match3.1,match3.2.1,match3.2.2]⟩
  have memory01 := Rlp.Validation.Above.trans source ready0 ready1 cursor.toNat above0 above1
  have memory02 := Rlp.Validation.Above.trans source ready1 ready2 cursor.toNat memory01 above2
  have memory03 := Rlp.Validation.Above.trans source ready2 ready3 cursor.toNat memory02 above3
  refine ⟨ready3,inner3,⟨results⟩,view3,memory03,?_,?_,?_,?_,run3,?_⟩
  · exact domain3.trans (domain2.trans (domain1.trans domain0))
  · exact endian3.trans (endian2.trans (endian1.trans endian0))
  · exact code3.trans (code2.trans (code1.trans code0))
  · exact heap3.trans (heap2.trans (heap1.trans heap0))
  · rw [restore0,restore1,restore2,restore3]
    rfl

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.fields_normal
