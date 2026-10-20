import InitECandidate.Solver.Input.MainInitializationGlobals
import InitECandidate.Solver.Input.MainRipemdInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterRipemd : ProgHOL 64 := match afterBls with | .seq _ rest => rest | _ => .skip
def ripemdState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := {RipemdInitialization.template (blsState source) 2713729752 with clock := source.clock - 27}

theorem after_bls_shape : afterBls = .seq (.call (some (none,none)) (ofString "ripemd160_init") []) afterRipemd := by
  simp only [afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterRipemd,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem rmd_tab_fresh : touchedBls.all (fun name => decide (ofString "rmd_tab" ≠ ofString name)) = true := by decide_cbv

theorem rmd_tab_before (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    (blsState middle).globals.lookup (ofString "rmd_tab") = some (.val (.word 0#64)) := by
  apply bls_initial_zero input source mptMiddle middle entry mpt reached _ (RipemdInitialization.symbol_member "rmd_tab" (by simp [RipemdInitialization.symbols]))
  intro name member
  exact of_decide_eq_true (List.all_eq_true.mp rmd_tab_fresh name member)

theorem ripemd_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) : InitializerAllocations.context (ripemdState source) = InitializerAllocations.context source :=
  (InitializerAllocations.context_clock (RipemdInitialization.template (blsState source) 2713729752) (source.clock - 27)).trans
    ((RipemdInitialization.template_context (blsState source) 2713729752).trans (bls_context source))

theorem ripemd_heap (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) :
    (ripemdState middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730208#64)) := RipemdInitialization.template_heap (blsState middle) 2713729752 (bls_heap source mptMiddle middle reached)

theorem ripemd_scalars (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : OriginalScalarGlobals.Scalars (ripemdState middle).globals :=
  RipemdInitialization.template_scalars (blsState middle) 2713729752 (bls_scalars input source mptMiddle middle entry mpt reached)

theorem ripemd_spent (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) (funded : 27 ≤ middle.clock) :
    (ripemdState middle).clock ≤ source.clock ∧ source.clock - (ripemdState middle).clock ≤ 474 := by
  have current : (ripemdState middle).clock = middle.clock - 27 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

private theorem clock_override (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : Nat) :
    {{source with clock := first} with clock := second} = {source with clock := second} := rfl

private theorem ripemd_at_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "rmd_tab") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 456 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 5 ≤ clock) :
    evaluateHOLFiniteState {source with clock := clock} (.call (some (none,none)) (ofString "ripemd160_init") []) =
      (none,{RipemdInitialization.template source cursor with clock := clock - 5}) := by
  have actual := RipemdInitialization.call_execute {source with clock := clock} cursor installed scalars heap zero domain lower room aligned enough
  conv_rhs at actual => rw [RipemdInitialization.template_clock source cursor clock,clock_override (RipemdInitialization.template source cursor) clock (clock - 5)]
  exact actual

theorem ripemd_prefix (input : Guest.InputBlob) (source mptMiddle middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (blsState middle) afterBls = (result,target)) (notTimeout : result ≠ some .timeOut) :
    27 ≤ middle.clock ∧ evaluateHOLFiniteState (ripemdState middle) afterRipemd = (result,target) := by
  let ready := blsState middle
  have installed : OriginalCode.Installed ready.code := by rw [bls_code source mptMiddle middle mpt reached]; exact entry.code
  have scalars := bls_scalars input source mptMiddle middle entry mpt reached
  have heap := bls_heap source mptMiddle middle reached
  have zero := rmd_tab_before input source mptMiddle middle entry mpt reached
  have domain := bls_domain input source mptMiddle middle entry mpt reached
  have execute (clock : Nat) (enough : 5 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "ripemd160_init") []) =
        (none,{RipemdInitialization.template ready 2713729752 with clock := clock - 5}) := by
    exact ripemd_at_clock ready 2713729752 clock installed scalars heap zero domain (by decide) (by decide) (by decide) enough
  rw [after_bls_shape] at run
  obtain ⟨funded,remaining⟩ := terminating_prefix ready target (RipemdInitialization.template ready 2713729752) _ afterRipemd 5 result execute run notTimeout
  have positive : 27 ≤ middle.clock := by change 5 ≤ middle.clock - 22 at funded; omega
  have clock : ready.clock - 5 = middle.clock - 27 := by change middle.clock - 22 - 5 = _; omega
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_ripemd (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle middle ∧ 27 ≤ middle.clock ∧
      evaluateHOLFiniteState (ripemdState middle) afterRipemd = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,_,run,classified,observation⟩ := reached_bls input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨funded,remaining⟩ := ripemd_prefix input source mptMiddle middle target entry mpt reached result run notTimeout
  exact ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_bls_shape
#print axioms InitECandidate.Solver.Input.Main.rmd_tab_fresh
#print axioms InitECandidate.Solver.Input.Main.rmd_tab_before
#print axioms InitECandidate.Solver.Input.Main.ripemd_context
#print axioms InitECandidate.Solver.Input.Main.ripemd_heap
#print axioms InitECandidate.Solver.Input.Main.ripemd_scalars
#print axioms InitECandidate.Solver.Input.Main.ripemd_spent
#print axioms InitECandidate.Solver.Input.Main.ripemd_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_ripemd
