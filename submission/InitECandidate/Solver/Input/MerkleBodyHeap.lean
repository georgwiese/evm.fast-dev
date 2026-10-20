import InitECandidate.Solver.Input.MerkleNonemptyHeap
import InitECandidate.Solver.Input.MerkleZeroBound

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual normal return of unchanged merkleize restores its entry
heap cursor, including empty trees. The proof uses current geometry and
the real saved mark/release; no future normal helper run is assumed. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor stp accel : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (workspace : ShaPair.Workspace source stp accel)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
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
  have returnedHeap : final.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
    by_cases zero : n.toNat=0
    · have nZero : n=0#64 := BitVec.eq_of_toNat_eq (by simpa using zero)
      have zeroCount : current.locals.lookup (ofString "n")=some (.val (.word 0#64)) := by
        simpa [zero] using currentCount
      have outputEq : evaluateHOLFiniteState current afterDepth=evaluateHOLFiniteState current zeroBody := by
        rw [zero_shape,evaluateHOLFiniteState_seq_line780,zero_guard_selected current zeroCount]
        have stops := zero_body_stops current
        generalize observed : evaluateHOLFiniteState current zeroBody=output at stops ⊢
        obtain ⟨result,target⟩ := output
        cases result with
        | none=>exact (stops rfl).elim
        | some result=>rfl
      rw [outputEq] at remaining
      have pure : GlobalEffects.Preserves (ofString "heap_ptr") current.code zeroBody := by
        unfold zeroBody
        exact GlobalEffects.sequence (ofString "heap_ptr") current.code _ _
          (GlobalEffects.call_body (ofString "heap_ptr") current.code (some none) (ofString "memcpy") zeroArguments CopyGeneral.formals Copy32.body .one
            (CopyGeneral.original_code current.code currentWorkspace.installed) (Copy32.globals (ofString "heap_ptr") current.code))
          (GlobalEffects.returned (ofString "heap_ptr") current.code _)
      have frame := pure current rfl
      rw [remaining] at frame
      have finalHeap : final.globals.lookup (ofString "heap_ptr")=current.globals.lookup (ofString "heap_ptr") := congrArg Prod.snd frame
      exact finalHeap.trans (by rw [currentGlobals]; exact heap)
    · exact nonempty_tail_return_heap current final p cursor stp accel n.toNat dn (by omega) (by omega) countPower currentWorkspace
        ((other "p" (by decide) (by decide) (by decide)).trans pointer) currentCount currentDepth
        (by rw [currentGlobals]; exact heap) inputArena currentArena aligned value remaining
  have endpointGlobals : post.globals=final.globals := by
    have h:=congrArg PanSemStateFiniteExact.globals (restored final)
    rw [endpoint]
    exact h
  rw [endpointGlobals]
  exact returnedHeap

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.body_return_heap
