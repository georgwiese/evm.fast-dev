import InitECandidate.Solver.WitnessRadix.Keccak256Allocated

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Environment.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp scratch : BitVec 64)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source) (environment : Environment source stp scratch) :
    Environment target stp scratch := by
  have globals : target.globals=source.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
    exact h
  have codes : target.code=source.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control
    exact h
  have domain : target.memaddrs=source.memaddrs := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
    exact h
  constructor
  · exact domain.trans environment.domain
  · simpa only [globals] using environment.stateGlobal
  · simpa only [globals] using environment.scratchGlobal
  · simpa only [codes] using environment.zeroCode
  · simpa only [codes] using environment.copyCode
  · exact Code.of_control source target control environment.hashCode

end InitECandidate.Solver.WitnessRadix.Keccak256


#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Environment.of_control
