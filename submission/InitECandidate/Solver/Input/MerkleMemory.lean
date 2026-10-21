import InitECandidate.Solver.Input.MerkleNonemptyMemory
import InitECandidate.Solver.Input.SszHashProtected
import InitECandidate.Solver.Input.MerkleCallCost

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole unchanged original merkleize preserves a copied/decoded word
below its real temporary cursor and outside its caller output. Prefix
logarithms, empty copy, all normal hash loops and heap scopes are included. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out stp accel chunk zeros query : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  let workspace := protection.workspace.sha
  have notTimeout : some (.returned value)≠some (.timeOut : PanSemResultExact 64) := by simp
  obtain ⟨current,final,dl,dn,restoration,dlBound,dnBound,limitPower,countPower,dlPrevious,dnPrevious,dnSize,locals,paid,clock,cost,frame,remaining,endpoint,restored⟩ :=
    depth_prefix source post n limit depth small countBound limitBound workspace.installed count limitLocal (some (.returned value)) run notTimeout
  have other (name : String) (dlOther : ofString "dl"≠ofString name) (dnOther : ofString "dn"≠ofString name) (targetOther : ofString "target"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,dlOther,dnOther,targetOther]
  have currentCount : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n.toNat))) := by
    simpa using (other "n" (by decide) (by decide) (by decide)).trans count
  have currentDepth : current.locals.lookup (ofString "dn")=some (.val (.word (BitVec.ofNat 64 dn))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "target"≠ofString "dn" from by decide]
  have currentTarget : current.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 (max dl dn)))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have currentCode : current.code=source.code := by have h:=congrArg PanSemStateFiniteExact.code frame; exact h
  have currentDomain : current.memaddrs=source.memaddrs := by have h:=congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have currentGlobals : current.globals=source.globals := by have h:=congrArg PanSemStateFiniteExact.globals frame; exact h
  have currentWorkspace := ShaPair.Workspace.of_fields source current stp accel workspace currentCode currentDomain
    (by rw [currentGlobals]) (by rw [currentGlobals])
  have targetBound : max dl dn≤depth := Nat.max_le.mpr ⟨dlBound,dnBound⟩
  have currentArena := AllocatedBytes.Arena.weaken cursor (32*max 1 (2*n.toNat)) (32*2^dn) bufferArena (by omega)
  have currentMemory : current.memory query=source.memory query := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory query) frame
    exact h
  have currentOutput := (other "out" (by decide) (by decide) (by decide)).trans output
  have currentTable : current.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) := by rw [currentGlobals]; exact protection.workspace.zerosLocal
  have currentAway : CopyGeneral.Away cursor query (32*2^dn) := CopyGeneral.Away.after cursor query (32*2^dn) aligned (by have h:=currentArena.upper; omega) below
  have finalMemory : final.memory query=current.memory query := by
    by_cases zero : n.toNat=0
    · have nZero : n=0#64 := BitVec.eq_of_toNat_eq (by simpa using zero)
      have zeroCount : current.locals.lookup (ofString "n")=some (.val (.word 0#64)) := by simpa [zero] using currentCount
      have selected : evaluateHOLFiniteState current afterDepth=evaluateHOLFiniteState current zeroBody := by
        rw [zero_shape,evaluateHOLFiniteState_seq_line780,zero_guard_selected current zeroCount]
        have stops := zero_body_stops current
        generalize observed : evaluateHOLFiniteState current zeroBody=response at stops ⊢
        obtain ⟨result,target⟩ := response
        cases result with
        | none=>exact (stops rfl).elim
        | some result=>rfl
      rw [selected] at remaining
      have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) zeroArguments=
          some (CopyGeneral.values out (zeros+BitVec.ofNat 64 (32*max dl dn)) 32) := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,localVar,currentOutput,currentTarget,currentTable,CopyGeneral.values,
          valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
      have inputZero := AllocatedBytes.Arena.subrange zeros 2048 (32*max dl dn) 32 protection.workspace.zeroArena (by omega)
      exact MemoryAt.copy_returned current final zeroArguments _ out query 32 currentWorkspace.installed currentWorkspace.domain args inputZero outArena outAway value remaining
    · exact nonempty_tail_memory current final p cursor out zeros stp accel query n.toNat dn (max dl dn) (by omega) (by omega) (Nat.le_max_right _ _) countPower currentWorkspace
        ((other "p" (by decide) (by decide) (by decide)).trans pointer) currentCount currentOutput currentDepth currentTarget
        (by rw [currentGlobals]; exact heap) currentTable inputArena currentArena aligned outArena protection.workspace.zeroArena protection.stateAway protection.accelAway currentAway outAway value remaining
  have endpointMemory : post.memory query=final.memory query := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory query) (restored final)
    rw [endpoint]
    exact h
  exact endpointMemory.trans (finalMemory.trans currentMemory)

/-- Real normal original Merkle caller inherits the complete protected word
frame at its actual four-word ABI and current temporary/output geometry. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out stp accel chunk zeros query : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n limit out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal,limitCell,outLocal⟩ := environment source.code.lookup p n limit out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "merkleize") arguments (values p n limit out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p n limit cursor out stp accel chunk zeros query depth small countBound limitBound
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) pLocal nLocal limitCell outLocal heap inputArena bufferArena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.body_memory
#print axioms InitECandidate.Solver.Input.Merkle.call_memory
