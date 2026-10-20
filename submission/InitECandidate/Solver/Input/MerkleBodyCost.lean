import InitECandidate.Solver.Input.MerkleNonemptyTail
import InitECandidate.Solver.Input.MerkleZeroBound

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole unchanged nonempty merkleize, including actual depth calculations,
allocation, copies, every dense pair, extension and heap release. The memory
premise scales with the actual count, not the declared limit. -/
theorem nonempty_body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out zeros stp accel : BitVec 64) (depth : Nat)
    (positive : 0<n.toNat) (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (workspace : ShaPair.Workspace source stp accel)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n.toNat+55*depth+13 := by
  obtain ⟨current,final,dl,dn,restoration,dlBound,dnBound,limitPower,countPower,dlPrevious,dnPrevious,dnSize,locals,paid,clock,cost,frame,remaining,endpoint,restored⟩ :=
    depth_prefix source post n limit depth small countBound limitBound workspace.installed count limitLocal result run notTimeout
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
  have tailCost := nonempty_tail_cost current final p cursor out zeros stp accel n.toNat dn (max dl dn) positive (by omega) (Nat.le_max_right _ _) countPower currentWorkspace
    ((other "p" (by decide) (by decide) (by decide)).trans pointer) currentCount
    ((other "out" (by decide) (by decide) (by decide)).trans output) currentDepth currentTarget
    (by rw [currentGlobals]; exact heap) (by rw [currentGlobals]; exact table)
    inputArena currentArena aligned outputArena tableArena result remaining notTimeout
  have finalLe := evaluateHOLFiniteState_clock_le current afterDepth
  rw [remaining] at finalLe
  change final.clock≤current.clock at finalLe
  have endpointClock : post.clock=final.clock := by
    have h:=congrArg PanSemStateFiniteExact.clock (restored final)
    rw [endpoint]
    exact h
  have sizeBound : 2^dn≤2*n.toNat := by rw [Nat.max_eq_right (by omega)] at dnSize; exact dnSize
  rw [endpointClock]
  omega

/-- A current-state bound for every non-timeout original Merkle outcome,
including the actual empty branch. This is a source-clock bound. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p n limit cursor out zeros stp accel : BitVec 64) (depth : Nat)
    (small : depth<64) (countBound : n.toNat≤2^depth) (limitBound : limit.toNat≤2^depth)
    (workspace : ShaPair.Workspace source stp accel)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (inputArena : AllocatedBytes.Arena p (32*n.toNat))
    (bufferArena : AllocatedBytes.Arena cursor (32*max 1 (2*n.toNat))) (aligned : cursor.toNat%8=0)
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n.toNat+55*depth+13 := by
  by_cases zero : n.toNat=0
  · have nZero : n=0#64 := BitVec.eq_of_toNat_eq (by simpa using zero)
    have cost := empty_bound source post limit out zeros depth small limitBound workspace.installed workspace.domain
      (nZero ▸ count) limitLocal output table outputArena tableArena result run notTimeout
    omega
  · exact nonempty_body_cost source post p n limit cursor out zeros stp accel depth (by omega) small countBound limitBound workspace pointer count limitLocal output heap table inputArena bufferArena aligned outputArena tableArena result run notTimeout

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.nonempty_body_cost
#print axioms InitECandidate.Solver.Input.Merkle.body_cost
