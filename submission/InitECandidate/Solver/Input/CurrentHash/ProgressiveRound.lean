import InitECandidate.Solver.Input.CurrentHash.ProgressiveEntry
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveRound
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive

/-- Actual progressive counter/pointer bindings, without a future run, mapped
arena, allocator room or obsolete accelerator workspace. -/
structure Round (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat) : Prop where
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  rootsLocal : source.locals.lookup (ofString "roots") = some (.val (.word roots))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  position : source.locals.lookup (ofString "off") = some (.val (.word (BitVec.ofNat 64 (offset k))))
  sizeLocal : source.locals.lookup (ofString "size") = some (.val (.word (BitVec.ofNat 64 (4^k))))
  round : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))

theorem Round.pair {source : PanSemStateFiniteExact 64 Guest.HostMemory} {p roots : BitVec 64} {n k : Nat}
    (data : Round source p roots n k) : Round (pairEntry source n (offset k) (4^k)) p roots n k :=
  ⟨(pair_entry_other source n (offset k) (4^k) "p" (by decide)).trans data.pointer,
    (pair_entry_other source n (offset k) (4^k) "roots" (by decide)).trans data.rootsLocal,
    (pair_entry_other source n (offset k) (4^k) "n" (by decide)).trans data.count,
    (pair_entry_other source n (offset k) (4^k) "off" (by decide)).trans data.position,
    (pair_entry_other source n (offset k) (4^k) "size" (by decide)).trans data.sizeLocal,
    (pair_entry_other source n (offset k) (4^k) "k" (by decide)).trans data.round⟩

theorem Round.dec_clock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {p roots : BitVec 64} {n k : Nat}
    (data : Round source p roots n k) : Round (decClockHOLFinite source) p roots n k :=
  ⟨data.pointer, data.rootsLocal, data.count, data.position, data.sizeLocal, data.round⟩

theorem Round.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {p roots : BitVec 64} {n k : Nat}
    (data : Round source p roots n k) (function : MlS) (arguments : List (ExpHOL 64))
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) : Round post p roots n k := by
  have kept (name : MlS) : post.locals.lookup name = source.locals.lookup name := CallNormal.ignored_lookup source post name function arguments actual
  exact ⟨(kept _).trans data.pointer, (kept _).trans data.rootsLocal, (kept _).trans data.count,
    (kept _).trans data.position, (kept _).trans data.sizeLocal, (kept _).trans data.round⟩

/-- The same real inner call and updates establish the next geometric round.
Only actual normal continuation supplies the next bindings. -/
theorem after_cap_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (data : Round source p roots n k) (actual : evaluateHOLFiniteState source afterCap = (none, post)) : Round post p roots n (k+1) := by
  obtain ⟨middle, called, continued⟩ := sequence_none source post _ updates actual
  have current := data.after_call _ _ called
  have advancedRun := updates_execute middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) current.position current.sizeLocal current.round
  rw [continued] at advancedRun
  have postEq : post = advanced middle (BitVec.ofNat 64 (offset k)) (BitVec.ofNat 64 (4^k)) (BitVec.ofNat 64 k) := congrArg Prod.snd advancedRun
  have kept (name : String) (notOff : ofString name ≠ ofString "off") (notSize : ofString name ≠ ofString "size") (notK : ofString name ≠ ofString "k") :
      post.locals.lookup (ofString name) = middle.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) updates := .seq (.assign _ _ notOff) (.seq (.assign _ _ notSize) (.assign _ _ notK))
    have summary := safe.summary_full middle
    unfold LocalSummary at summary
    rw [continued] at summary
    exact summary.1 rfl
  have geometry := advanced_geometry middle k
  rw [←postEq] at geometry
  exact ⟨(kept "p" (by decide) (by decide) (by decide)).trans current.pointer,
    (kept "roots" (by decide) (by decide) (by decide)).trans current.rootsLocal,
    (kept "n" (by decide) (by decide) (by decide)).trans current.count, geometry.1, geometry.2.1, geometry.2.2⟩

theorem step_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (active : offset k < n) (data : Round source p roots n k)
    (actual : evaluateHOLFiniteState source step = (none, post)) : Round post p roots n (k+1) := by
  obtain ⟨round, depth, power, sizeBound, positive⟩ := round_geometry n k bounded active
  rw [step_prefix source n (offset k) (4^k) (by omega) (by omega) (by omega) data.count data.position data.sizeLocal] at actual
  let entry := pairEntry source n (offset k) (4^k)
  let final := (evaluateHOLFiniteState entry afterCap).2
  have observed := congrArg Prod.fst actual
  have remaining : evaluateHOLFiniteState entry afterCap = (none, final) := Prod.ext observed rfl
  have endpoint : post = restore source "cnt" final := (congrArg Prod.snd actual).symm
  have next := after_cap_normal entry final p roots n k data.pair remaining
  have kept (name : String) (different : ofString name ≠ ofString "cnt") : post.locals.lookup (ofString name) = final.locals.lookup (ofString name) := by
    rw [endpoint]
    exact restore_lookup_other source final "cnt" name different
  exact ⟨(kept "p" (by decide)).trans next.pointer, (kept "roots" (by decide)).trans next.rootsLocal,
    (kept "n" (by decide)).trans next.count, (kept "off" (by decide)).trans next.position,
    (kept "size" (by decide)).trans next.sizeLocal, (kept "k" (by decide)).trans next.round⟩

end InitECandidate.Solver.Input.CurrentHash.ProgressiveRound

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveRound.Round.pair
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveRound.Round.dec_clock
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveRound.Round.after_call
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveRound.after_cap_normal
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveRound.step_normal
