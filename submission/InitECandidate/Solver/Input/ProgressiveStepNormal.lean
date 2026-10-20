import InitECandidate.Solver.Input.ProgressiveRound

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem merkle_call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "merkleize") arguments) :=
  GlobalEffects.call_body key code (some none) (ofString "merkleize") arguments Merkle.formals Merkle.body .one
    (Merkle.original_code code installed) (Merkle.globals key code installed other)

/-- A real normal inner Merkle call retains all current round bindings and
restores its actual heap cursor; it assumes neither outcome in advance. -/
theorem round_after_merkle (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n) (actual : RoundState source p roots cursor zeros stp accel n k)
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (mapped : Geometry p roots cursor zeros n)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") arguments)=(none,post)) :
    RoundState post p roots cursor zeros stp accel n k := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  obtain ⟨inputArena,outputArena,bufferArena⟩ := pair_geometry p roots cursor zeros n k bounded active mapped
  have countBound := Nat.min_le_left (4^k) (n-offset k)
  have countNumber : (BitVec.ofNat 64 (min (4^k) (n-offset k))).toNat=min (4^k) (n-offset k) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sizeNumber : (BitVec.ofNat 64 (4^k)).toNat=4^k := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args := merkle_arguments source p roots (offset k) (min (4^k) (n-offset k)) (4^k) k
    actual.pointer actual.rootsLocal actual.position countLocal actual.sizeLocal actual.round
  have heap := Merkle.ignored_return_heap source post (p+BitVec.ofNat 64 (32*offset k)) (BitVec.ofNat 64 (min (4^k) (n-offset k)))
    (BitVec.ofNat 64 (4^k)) cursor (roots+BitVec.ofNat 64 (32*k)) stp accel (2*k) depth
    (by rw [countNumber,←power]; exact countBound) (by rw [sizeNumber,←power]) actual.workspace actual.heap
    (by rw [countNumber]; exact inputArena) (by rw [countNumber]; exact bufferArena) mapped.aligned arguments args run
  obtain ⟨funded,values,body,callee,shape,target,returned,argsRead,called,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "merkleize") arguments run
  have locals : post.locals=source.locals := by rw [endpoint]
  have tableFrame := merkle_call_globals (ofString "zero_hashes") source.code actual.workspace.installed (by decide) source rfl
  rw [run] at tableFrame
  have table : post.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) := (congrArg Prod.snd tableFrame).trans actual.table
  have workspace := ShaPair.Workspace.after source post stp accel actual.workspace _ none run
    (merkle_call_globals (ofString "sha_st") source.code actual.workspace.installed (by decide))
    (merkle_call_globals (ofString "sha_accel") source.code actual.workspace.installed (by decide))
  exact ⟨by rw [locals]; exact actual.pointer,by rw [locals]; exact actual.rootsLocal,by rw [locals]; exact actual.count,
    by rw [locals]; exact actual.position,by rw [locals]; exact actual.sizeLocal,by rw [locals]; exact actual.round,heap,table,workspace⟩

/-- The actual continuing cap/call/update sequence establishes precisely the
next geometric round, with its real restored heap and original workspace. -/
theorem after_cap_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n) (actual : RoundState source p roots cursor zeros stp accel n k)
    (countLocal : source.locals.lookup (ofString "cnt")=some (.val (.word (BitVec.ofNat 64 (min (4^k) (n-offset k))))))
    (mapped : Geometry p roots cursor zeros n) (run : evaluateHOLFiniteState source afterCap=(none,post)) :
    RoundState post p roots cursor zeros stp accel n (k+1) := by
  obtain ⟨middle,called,continued⟩ := sequence_none source post _ updates run
  have current := round_after_merkle source middle p roots cursor zeros stp accel n k bounded active actual countLocal mapped called
  have advancedRun := updates_execute middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) current.position current.sizeLocal current.round
  rw [continued] at advancedRun
  have postEq : post=advanced middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) := congrArg Prod.snd advancedRun
  have advancedOther (name : String) (a : ofString name≠ofString "off") (b : ofString name≠ofString "size") (c : ofString name≠ofString "k") :
      post.locals.lookup (ofString name)=middle.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) updates := .seq (.assign _ _ a) (.seq (.assign _ _ b) (.assign _ _ c))
    have summary := safe.summary_full middle
    unfold LocalSummary at summary
    rw [continued] at summary
    exact summary.1 rfl
  have geo := advanced_geometry middle k
  rw [←postEq] at geo
  have workspace := ShaPair.Workspace.of_fields middle post stp accel current.workspace (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl)
  exact ⟨(advancedOther "p" (by decide) (by decide) (by decide)).trans current.pointer,
    (advancedOther "roots" (by decide) (by decide) (by decide)).trans current.rootsLocal,
    (advancedOther "n" (by decide) (by decide) (by decide)).trans current.count,geo.1,geo.2.1,geo.2.2,
    by rw [postEq]; exact current.heap,by rw [postEq]; exact current.table,workspace⟩

/-- A real normal original body step establishes the next round after its
cnt scope is restored. No other current caller bindings are invented. -/
theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (active : offset k<n) (actual : RoundState source p roots cursor zeros stp accel n k)
    (mapped : Geometry p roots cursor zeros n) (run : evaluateHOLFiniteState source step=(none,post)) :
    RoundState post p roots cursor zeros stp accel n (k+1) := by
  obtain ⟨round,depth,power,sizeBound,positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) actual.count actual.position actual.sizeLocal] at run
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst run
  have remaining : evaluateHOLFiniteState entry afterCap=(none,final) := Prod.ext observed rfl
  have endpoint : post=restore source "cnt" final := (congrArg Prod.snd run).symm
  have next := after_cap_normal entry final p roots cursor zeros stp accel n k bounded active
    (RoundState.pair source p roots cursor zeros stp accel n k actual) (pair_entry_count source n (offset k) (4^k)) mapped remaining
  have other (name : String) (different : ofString name≠ofString "cnt") : post.locals.lookup (ofString name)=final.locals.lookup (ofString name) := by
    rw [endpoint]
    exact restore_lookup_other source final "cnt" name different
  have workspace := ShaPair.Workspace.of_fields final post stp accel next.workspace (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)
  exact ⟨(other "p" (by decide)).trans next.pointer,(other "roots" (by decide)).trans next.rootsLocal,(other "n" (by decide)).trans next.count,
    (other "off" (by decide)).trans next.position,(other "size" (by decide)).trans next.sizeLocal,(other "k" (by decide)).trans next.round,
    by rw [endpoint]; exact next.heap,by rw [endpoint]; exact next.table,workspace⟩

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.merkle_call_globals
#print axioms InitECandidate.Solver.Input.Progressive.round_after_merkle
#print axioms InitECandidate.Solver.Input.Progressive.after_cap_normal
#print axioms InitECandidate.Solver.Input.Progressive.step_normal
