import InitECandidate.Solver.Input.RequestFromHeader
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current decoder metadata and aggregate source-clock allowance. Memory
and locals remain the actual phase-specific values. Only the heap global may
change across these parsing prefixes; the complete FFI state is retained. -/
structure ParserFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (price : Nat) : Prop where
  code : target.code = source.code
  exceptions : target.eshapes = source.eshapes
  structs : target.structs = source.structs
  domain : target.memaddrs = source.memaddrs
  shared : target.shMemaddrs = source.shMemaddrs
  endian : target.be = source.be
  ffi : target.ffi = source.ffi
  globals : target.globals = source.globals.update (ofString "heap_ptr",.val (.word heap))
  forward : target.clock ≤ source.clock
  clockLower : source.clock - price ≤ target.clock

namespace ParserFrame

theorem of_request (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (frame : Request.ReadyFrame source target cursor) (forward : target.clock ≤ source.clock) :
    ParserFrame source target (PersistentAlloc.rounded cursor 96#64) 5 :=
  ⟨frame.code,frame.exceptions,frame.structs,frame.domain,frame.shared,frame.endian,frame.ffi,frame.globals,forward,frame.clockLower⟩

/-- Compose a phase's actual metadata and clock facts with the established
parser prefix. No execution or successful future outcome is postulated. -/
theorem advance (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (oldHeap heap : BitVec 64) (price cost : Nat)
    (frame : ParserFrame source middle oldHeap price)
    (context : InitializerAllocations.context target = InitializerAllocations.context middle)
    (globals : target.globals = source.globals.update (ofString "heap_ptr",.val (.word heap)))
    (forward : target.clock ≤ middle.clock) (clockLower : middle.clock - cost ≤ target.clock) :
    ParserFrame source target heap (price + cost) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,globals,Nat.le_trans forward frame.forward,?_⟩
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) context
    exact same.trans frame.code
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.eshapes) context
    exact same.trans frame.exceptions
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.structs) context
    exact same.trans frame.structs
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) context
    exact same.trans frame.domain
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.shMemaddrs) context
    exact same.trans frame.shared
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) context
    exact same.trans frame.endian
  · have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi) context
    exact same.trans frame.ffi
  · have before := frame.clockLower
    omega

end ParserFrame
end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ParserFrame.of_request
#print axioms InitECandidate.Solver.Input.ParserFrame.advance
