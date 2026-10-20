import InitECandidate.Solver.Input.MerkleProgram

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Two actual original logarithm calls and the actual maximum call reach
the literal Merkle body with validated minimal depths. Funding and all data
come from the same observed execution; no hashing success is assumed. -/
theorem depth_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (n limit : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (installed : OriginalCode.Installed source.code)
    (countLocal : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    ∃ current final dl dn, ∃ restoration : PanSemStateFiniteExact 64 Guest.HostMemory→PanSemStateFiniteExact 64 Guest.HostMemory,
      dl≤depth ∧ dn≤depth ∧ limit.toNat≤2^dl ∧ n.toNat≤2^dn ∧
      (0<dl→2^(dl-1)<limit.toNat) ∧ (0<dn→2^(dn-1)<n.toNat) ∧ 2^dn≤max 1 (2*n.toNat) ∧
      current.locals=((source.locals.update (ofString "dl",.val (.word (BitVec.ofNat 64 dl)))).update
        (ofString "dn",.val (.word (BitVec.ofNat 64 dn)))).update (ofString "target",.val (.word (BitVec.ofNat 64 (max dl dn)))) ∧
      dl+dn+3≤source.clock ∧ current.clock=source.clock-(dl+dn+3) ∧ source.clock-current.clock≤2*depth+3 ∧
      CeilLog2.frozen current=CeilLog2.frozen source ∧ evaluateHOLFiniteState current afterDepth=(result,final) ∧
      post=restoration final ∧ (∀ target,emptyLocalsHOLFinite (restoration target)=emptyLocalsHOLFinite target) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "limit"]=some [.val (.word limit)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,limitLocal]
  rw [prefix_shape.1] at run
  obtain ⟨first,firstPost,dl,dlBound,limitPower,dlPrevious,dlSize,dlPaid,firstLocals,firstClock,firstFrame,firstRun,firstEndpoint⟩ :=
    CeilLog2.call_trace source post limit depth small limitBound "dl" [localVar "limit"] afterLimit args (CeilLog2.original_code source.code installed) result run notTimeout
  have firstCode : first.code=source.code := by have h := congrArg PanSemStateFiniteExact.code firstFrame; exact h
  have firstInstalled : OriginalCode.Installed first.code := firstCode.symm ▸ installed
  have nFirst : first.locals.lookup (ofString "n")=some (.val (.word n)) := by
    rw [firstLocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "dl"≠ofString "n" from by decide] using countLocal
  have dlFirst : first.locals.lookup (ofString "dl")=some (.val (.word (BitVec.ofNat 64 dl))) := by
    rw [firstLocals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have argsCount : evalListHOLFinite first (h:=fun address=>Classical.propDecidable (first.memaddrs address)) [localVar "n"]=some [.val (.word n)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nFirst]
  rw [prefix_shape.2.1] at firstRun
  obtain ⟨second,secondPost,dn,dnBound,countPower,dnPrevious,dnSize,dnPaid,secondLocals,secondClock,secondFrame,secondRun,secondEndpoint⟩ :=
    CeilLog2.call_trace first firstPost n depth small countBound "dn" [localVar "n"] afterCount argsCount (CeilLog2.original_code first.code firstInstalled) result firstRun notTimeout
  have secondCode : second.code=first.code := by have h := congrArg PanSemStateFiniteExact.code secondFrame; exact h
  have secondInstalled : OriginalCode.Installed second.code := secondCode.symm ▸ firstInstalled
  have dlSecond : second.locals.lookup (ofString "dl")=some (.val (.word (BitVec.ofNat 64 dl))) := by
    rw [secondLocals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "dn"≠ofString "dl" from by decide] using dlFirst
  have dnSecond : second.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by
    rw [secondLocals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have argsMax : evalListHOLFinite second (h:=fun address=>Classical.propDecidable (second.memaddrs address)) [localVar "dl",localVar "dn"]=
      some (UnsignedMax.values (BitVec.ofNat 64 dl) (BitVec.ofNat 64 dn)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dlSecond,dnSecond,UnsignedMax.values]
  rw [prefix_shape.2.2] at secondRun
  obtain ⟨maxPaid,final,maxRun,maxEndpoint⟩ := UnsignedMax.call_trace second secondPost (BitVec.ofNat 64 dl) (BitVec.ofNat 64 dn) "target" [localVar "dl",localVar "dn"] afterDepth
    argsMax (UnsignedMax.original_code second.code secondInstalled) result secondRun notTimeout
  have dlNumber : (BitVec.ofNat 64 dl).toNat=dl := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have dnNumber : (BitVec.ofNat 64 dn).toNat=dn := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have maxBound : max dl dn≤depth := Nat.max_le.mpr ⟨dlBound,dnBound⟩
  have selected : UnsignedMax.selected (BitVec.ofNat 64 dl) (BitVec.ofNat 64 dn)=BitVec.ofNat 64 (max dl dn) := by
    apply BitVec.eq_of_toNat_eq
    rw [UnsignedMax.selected_number,dlNumber,dnNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [selected] at maxRun
  let current := bind {second with clock:=second.clock-1} "target" (BitVec.ofNat 64 (max dl dn))
  let restoration := fun target=>restore source "dl" (restore first "dn" (restore second "target" target))
  have locals : current.locals=((source.locals.update (ofString "dl",.val (.word (BitVec.ofNat 64 dl)))).update
        (ofString "dn",.val (.word (BitVec.ofNat 64 dn)))).update (ofString "target",.val (.word (BitVec.ofNat 64 (max dl dn)))) := by
    change second.locals.update _=_
    rw [secondLocals,firstLocals]
  have currentClock : current.clock=second.clock-1 := rfl
  have paid : dl+dn+3≤source.clock := by omega
  have clock : current.clock=source.clock-(dl+dn+3) := by rw [currentClock]; omega
  have frozen : CeilLog2.frozen current=CeilLog2.frozen source := by
    change CeilLog2.frozen second=CeilLog2.frozen source
    exact secondFrame.trans firstFrame
  exact ⟨current,final,dl,dn,restoration,dlBound,dnBound,limitPower,countPower,dlPrevious,dnPrevious,dnSize,locals,paid,clock,
    by rw [clock]; omega,frozen,maxRun,by rw [firstEndpoint,secondEndpoint,maxEndpoint],by intro target; rfl⟩

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.depth_prefix
