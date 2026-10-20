import InitECandidate.Solver.Input.MainHeaderEntry
import InitECandidate.Solver.Input.MainHeaderInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterHeader : ProgHOL 64 := match afterBlake with | .seq _ rest => rest | _ => .skip
def headerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := {HeaderInitialization.template (blakeState source) 2713730616 with clock := source.clock - 35}

theorem after_blake_shape : afterBlake = .seq (.call (some (none,none)) (ofString "header_init") []) afterHeader := by
  simp only [afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterHeader,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem header_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) : InitializerAllocations.context (headerState source) = InitializerAllocations.context source :=
  (InitializerAllocations.context_clock (HeaderInitialization.template (blakeState source) 2713730616) (source.clock - 35)).trans
    ((HeaderInitialization.template_context (blakeState source) 2713730616).trans (blake_context source))

theorem header_heap (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) :
    (headerState middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730624#64)) := HeaderInitialization.template_heap (blakeState middle) 2713730616 (blake_heap source mptMiddle middle reached)

theorem header_scalars (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : OriginalScalarGlobals.Scalars (headerState middle).globals := by
  simp only [headerState]
  exact HeaderInitialization.template_scalars (blakeState middle) 2713730616 (blake_scalars input source mptMiddle middle entry mpt reached)

theorem header_spent (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) (funded : 35 ≤ middle.clock) :
    (headerState middle).clock ≤ source.clock ∧ source.clock - (headerState middle).clock ≤ 482 := by
  have current : (headerState middle).clock = middle.clock - 35 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

private theorem clock_override (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : Nat) :
    {{source with clock := first} with clock := second} = {source with clock := second} := rfl

private theorem header_at_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "hdr_zero8") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 8 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ clock) :
    evaluateHOLFiniteState {source with clock := clock} (.call (some (none,none)) (ofString "header_init") []) =
      (none,{HeaderInitialization.template source cursor with clock := clock - 4}) := by
  have actual := HeaderInitialization.call_execute {source with clock := clock} cursor installed scalars heap zero domain lower room aligned enough
  conv_rhs at actual => rw [HeaderInitialization.template_clock source cursor clock,clock_override (HeaderInitialization.template source cursor) clock (clock - 4)]
  exact actual

theorem header_prefix (input : Guest.InputBlob) (source mptMiddle middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (blakeState middle) afterBlake = (result,target)) (notTimeout : result ≠ some .timeOut) :
    35 ≤ middle.clock ∧ evaluateHOLFiniteState (headerState middle) afterHeader = (result,target) := by
  let ready := blakeState middle
  have installed : OriginalCode.Installed ready.code := by rw [blake_code source mptMiddle middle mpt reached]; exact entry.code
  have scalars := blake_scalars input source mptMiddle middle entry mpt reached
  have heap := blake_heap source mptMiddle middle reached
  have zero := hdr_zero8_before input source mptMiddle middle entry mpt reached
  have domain := blake_domain input source mptMiddle middle entry mpt reached
  have execute (clock : Nat) (enough : 4 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "header_init") []) =
        (none,{HeaderInitialization.template ready 2713730616 with clock := clock - 4}) :=
    header_at_clock ready 2713730616 clock installed scalars heap zero domain (by decide) (by decide) (by decide) enough
  rw [after_blake_shape] at run
  obtain ⟨funded,remaining⟩ := terminating_prefix ready target (HeaderInitialization.template ready 2713730616) _ afterHeader 4 result execute run notTimeout
  have positive : 35 ≤ middle.clock := by change 4 ≤ middle.clock - 31 at funded; omega
  have clock : ready.clock - 4 = middle.clock - 35 := by change middle.clock - 31 - 4 = _; omega
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_header (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle middle ∧ 35 ≤ middle.clock ∧
      evaluateHOLFiniteState (headerState middle) afterHeader = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,_,run,classified,observation⟩ := reached_blake input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨funded,remaining⟩ := header_prefix input source mptMiddle middle target entry mpt reached result run notTimeout
  exact ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_blake_shape
#print axioms InitECandidate.Solver.Input.Main.header_context
#print axioms InitECandidate.Solver.Input.Main.header_heap
#print axioms InitECandidate.Solver.Input.Main.header_scalars
#print axioms InitECandidate.Solver.Input.Main.header_spent
#print axioms InitECandidate.Solver.Input.Main.header_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_header
