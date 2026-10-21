import InitECandidate.Solver.Input.RequestListHashLoop
import InitECandidate.Solver.Input.HeapReleaseReturn

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem list_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots out : BitVec 64) (n : Nat)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) listArguments=some (PListChunks.values roots n (BitVec.ofNat 64 n) out) := by
  simp [listArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,root,count,output,PListChunks.values]

theorem after_loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (arena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterLoop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤115*n+24208 := by
  have args := list_arguments source roots out n actual.root actual.count actual.output
  have releaseCost : ClockCost.Bound source.code FixedHash.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code actual.workspace.sha.installed (some none) _) (ClockCost.returned source.code _)
  unfold afterLoop at run
  have price := ClockCost.sequence_terminating source post _ FixedHash.releaseSuffix (115*n+24207) 1
    (by intro observed target evaluated notTimeout
        exact PListChunks.call_cost source target roots cursor out (BitVec.ofNat 64 n) stp accel chunk zeros n bounded actual.workspace actual.heap rootsArena arena aligned outArena (some none) listArguments args observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        have fields := evaluation_fields source middle _ none normal
        have bounded := releaseCost middle fields.2.2.2
        rw [evaluated] at bounded
        exact bounded)
    result run notTimeout
  exact price

theorem after_loop_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor mark stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (rootsArena : AllocatedBytes.Arena roots (32*n)) (arena : AllocatedBytes.Arena cursor (832+64*n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLoop=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args := list_arguments source roots out n actual.root actual.count actual.output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold afterLoop at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ FixedHash.releaseSuffix value (safe.summary_full source).2.1 run
  have heap := PListChunks.ignored_return_heap source middle roots cursor out (BitVec.ofNat 64 n) stp accel chunk zeros n bounded actual.workspace actual.heap rootsArena arena aligned outArena listArguments args normal
  have nextMark := (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "htr_plist_chunks") listArguments normal).trans saved
  have fields := evaluation_fields source middle _ none normal
  exact HeapScope.release_return_heap middle post mark cursor (fields.2.2.2.symm ▸ actual.workspace.sha.installed) nextMark heap value remaining

/-- Actual complete request-record loop and list-hash/release suffix.
Normal exits retain their real round state before hashing produced roots. -/
theorem loop_suffix_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor mark stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (arena : AllocatedBytes.Arena cursor (832+64*n)) (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source loopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(kind.record.price+2)*(n-index)+115*n+24208 ∧
      (∀ value,result=some (.returned value) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark))) := by
  have price := ClockCost.sequence_terminating source post loop afterLoop ((kind.record.price+2)*(n-index)) (115*n+24208)
    (fun observed target evaluated notTimeout=>loop_cost source target kind p roots out cursor stp accel chunk zeros n index bounded inside actual geometry observed evaluated notTimeout)
    (by intro middle normal observed target evaluated notTimeout
        obtain ⟨position,nextBound,next⟩ := loop_normal source middle kind p roots out cursor stp accel chunk zeros n index bounded inside actual geometry normal
        exact after_loop_cost middle target kind p roots out cursor stp accel chunk zeros n position bounded next geometry.rootsArena arena geometry.aligned outArena observed evaluated notTimeout)
    result run notTimeout
  refine ⟨by simpa only [Nat.add_assoc] using price,?_⟩
  intro value returned
  have returning := run
  rw [returned] at returning
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post loop afterLoop value ((loop_local (ofString "mark") (by decide)).summary_full source).2.1 returning
  obtain ⟨position,nextBound,next⟩ := loop_normal source middle kind p roots out cursor stp accel chunk zeros n index bounded inside actual geometry normal
  have summary := (loop_local (ofString "mark") (by decide)).summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark := (summary.1 rfl).trans saved
  exact after_loop_return_heap middle post kind p roots out cursor mark stp accel chunk zeros n position bounded next nextMark geometry.rootsArena arena geometry.aligned outArena value remaining

theorem after_loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code afterLoop :=
  GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "htr_plist_chunks") listArguments PListChunks.formals PListChunks.body .one
      (PListChunks.original_code code installed) (PListChunks.globals key code installed different))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) (Merkle.release_globals key code different)) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.list_arguments
#print axioms InitECandidate.Solver.Input.RequestListHash.after_loop_cost
#print axioms InitECandidate.Solver.Input.RequestListHash.after_loop_return_heap
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_suffix_summary
#print axioms InitECandidate.Solver.Input.RequestListHash.after_loop_globals
