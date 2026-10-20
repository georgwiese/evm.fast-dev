import InitECandidate.Solver.Input.MerkleZero

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete original merkleize on an actually empty tree, including both
logarithms, maximum and the real zero-hash copy. The n logarithm is derived
to be zero; the declared limit contributes only its actual bit depth. -/
theorem empty_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (limit out zeros : BitVec 64) (depth : Nat)
    (small : depth<64) (limitBound : limit.toNat≤2^depth) (installed : OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (count : source.locals.lookup (ofString "n")=some (.val (.word 0#64)))
    (limitLocal : source.locals.lookup (ofString "limit")=some (.val (.word limit)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (outputArena : AllocatedBytes.Arena out 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤depth+8 := by
  obtain ⟨current,final,dl,dn,restoration,dlBound,dnBound,limitPower,countPower,dlPrevious,dnPrevious,dnSize,locals,paid,clock,cost,frame,remaining,endpoint,restored⟩ :=
    depth_prefix source post 0#64 limit depth small (by change 0≤2^depth; omega) limitBound installed count limitLocal result run notTimeout
  have dnZero : dn=0 := by
    by_contra positive
    have bad := dnPrevious (by omega : 0<dn)
    change 2^(dn-1)<0 at bad
    exact Nat.not_lt_zero _ bad
  have other (name : String) (dlOther : ofString "dl"≠ofString name) (dnOther : ofString "dn"≠ofString name) (targetOther : ofString "target"≠ofString name) :
      current.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,dlOther,dnOther,targetOther]
  have currentCount := (other "n" (by decide) (by decide) (by decide)).trans count
  have currentOutput := (other "out" (by decide) (by decide) (by decide)).trans output
  have currentDepth : current.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 (max dl dn)))) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have currentCode : current.code=source.code := by have h := congrArg PanSemStateFiniteExact.code frame; exact h
  have currentDomain : current.memaddrs=source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have currentGlobals : current.globals=source.globals := by have h := congrArg PanSemStateFiniteExact.globals frame; exact h
  have targetSmall : max dl dn<64 := by have bound := Nat.max_le.mpr ⟨dlBound,dnBound⟩; omega
  have tailCost := after_depth_zero_cost current out zeros (max dl dn) targetSmall (currentCode.symm ▸ installed) (currentDomain.trans domain)
    currentCount currentOutput currentDepth (by rw [currentGlobals]; exact table) outputArena tableArena
  rw [remaining] at tailCost
  change current.clock-final.clock≤5 at tailCost
  have finalClock := evaluateHOLFiniteState_clock_le current afterDepth
  rw [remaining] at finalClock
  change final.clock≤current.clock at finalClock
  have endpointClock : post.clock=final.clock := by
    have h := congrArg PanSemStateFiniteExact.clock (restored final)
    rw [endpoint]
    exact h
  rw [endpointClock]
  omega

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.empty_bound
