import InitECandidate.Solver.Input.MainBlakeEntry
import InitECandidate.Solver.Input.MainBlakeInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterBlake : ProgHOL 64 := match afterRipemd with | .seq _ rest => rest | _ => .skip
def blakeState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := {BlakeInitialization.template (ripemdState source) 2713730208 with clock := source.clock - 31}

theorem after_ripemd_shape : afterRipemd = .seq (.call (some (none,none)) (ofString "blake2_init") []) afterBlake := by
  simp only [afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterBlake,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem blake_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) : InitializerAllocations.context (blakeState source) = InitializerAllocations.context source :=
  (InitializerAllocations.context_clock (BlakeInitialization.template (ripemdState source) 2713730208) (source.clock - 31)).trans
    ((BlakeInitialization.template_context (ripemdState source) 2713730208).trans (ripemd_context source))

theorem blake_heap (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) :
    (blakeState middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730616#64)) := BlakeInitialization.template_heap (ripemdState middle) 2713730208 (ripemd_heap source mptMiddle middle reached)

theorem blake_scalars (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : OriginalScalarGlobals.Scalars (blakeState middle).globals := by
  simp only [blakeState]
  exact BlakeInitialization.template_scalars (ripemdState middle) 2713730208 (ripemd_scalars input source mptMiddle middle entry mpt reached)

theorem blake_spent (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) (funded : 31 ≤ middle.clock) :
    (blakeState middle).clock ≤ source.clock ∧ source.clock - (blakeState middle).clock ≤ 478 := by
  have current : (blakeState middle).clock = middle.clock - 31 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

private theorem clock_override (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : Nat) :
    {{source with clock := first} with clock := second} = {source with clock := second} := rfl

private theorem blake_at_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "b2_sigma") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 408 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 4 ≤ clock) :
    evaluateHOLFiniteState {source with clock := clock} (.call (some (none,none)) (ofString "blake2_init") []) =
      (none,{BlakeInitialization.template source cursor with clock := clock - 4}) := by
  have actual := BlakeInitialization.call_execute {source with clock := clock} cursor installed scalars heap zero domain lower room aligned enough
  conv_rhs at actual => rw [BlakeInitialization.template_clock source cursor clock,clock_override (BlakeInitialization.template source cursor) clock (clock - 4)]
  exact actual

theorem blake_prefix (input : Guest.InputBlob) (source mptMiddle middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (ripemdState middle) afterRipemd = (result,target)) (notTimeout : result ≠ some .timeOut) :
    31 ≤ middle.clock ∧ evaluateHOLFiniteState (blakeState middle) afterBlake = (result,target) := by
  let ready := ripemdState middle
  have installed : OriginalCode.Installed ready.code := by rw [ripemd_code source mptMiddle middle mpt reached]; exact entry.code
  have scalars := ripemd_scalars input source mptMiddle middle entry mpt reached
  have heap := ripemd_heap source mptMiddle middle reached
  have zero := b2_sigma_before input source mptMiddle middle entry mpt reached
  have domain := ripemd_domain input source mptMiddle middle entry mpt reached
  have execute (clock : Nat) (enough : 4 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "blake2_init") []) =
        (none,{BlakeInitialization.template ready 2713730208 with clock := clock - 4}) :=
    blake_at_clock ready 2713730208 clock installed scalars heap zero domain (by decide) (by decide) (by decide) enough
  rw [after_ripemd_shape] at run
  obtain ⟨funded,remaining⟩ := terminating_prefix ready target (BlakeInitialization.template ready 2713730208) _ afterBlake 4 result execute run notTimeout
  have positive : 31 ≤ middle.clock := by change 4 ≤ middle.clock - 27 at funded; omega
  have clock : ready.clock - 4 = middle.clock - 31 := by change middle.clock - 27 - 4 = _; omega
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_blake (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle middle ∧ 31 ≤ middle.clock ∧
      evaluateHOLFiniteState (blakeState middle) afterBlake = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,_,run,classified,observation⟩ := reached_ripemd input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨funded,remaining⟩ := blake_prefix input source mptMiddle middle target entry mpt reached result run notTimeout
  exact ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_ripemd_shape
#print axioms InitECandidate.Solver.Input.Main.blake_context
#print axioms InitECandidate.Solver.Input.Main.blake_heap
#print axioms InitECandidate.Solver.Input.Main.blake_scalars
#print axioms InitECandidate.Solver.Input.Main.blake_spent
#print axioms InitECandidate.Solver.Input.Main.blake_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_blake
