import InitECandidate.Solver.WitnessRadix.ConstructorRecordStep

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

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact BackingLayout
open Flapjack.Basis.Pure.MlString

structure HashContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (sliceFor : BitVec 64 → Graph.Slice)
    (stp padScratch hashScratch : BitVec 64) (maximum : Nat) : Prop where
  scratchGlobal : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hashScratch))
  code : source.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one)
  environment : Keccak256.Environment source stp padScratch
  buffers : ∀ index<layout.count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 padScratch hashScratch (sliceFor (BitVec.ofNat 64 index)).2.toNat
  before : ∀ pool,stp.toNat+200≤(base layout pool).toNat ∧ padScratch.toNat+136≤(base layout pool).toNat ∧ hashScratch.toNat+32≤(base layout pool).toNat
  scratchAligned : hashScratch.toNat%8=0
  little : source.be=false
  lengthBound : ∀ index<layout.count,(sliceFor (BitVec.ofNat 64 index)).2.toNat≤maximum

theorem HashContext.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (sliceFor : BitVec 64 → Graph.Slice)
    (stp padScratch hashScratch : BitVec 64) (maximum : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source)
    (context : HashContext source layout sliceFor stp padScratch hashScratch maximum) : HashContext target layout sliceFor stp padScratch hashScratch maximum := by
  have globals : target.globals=source.globals := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
    exact h
  have codes : target.code=source.code := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control
    exact h
  have endian : target.be=source.be := by
    have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) control
    exact h
  constructor
  · simpa only [globals] using context.scratchGlobal
  · simpa only [codes] using context.code
  · exact Keccak256.Environment.of_control source target _ _ control context.environment
  · exact context.buffers
  · exact context.before
  · exact context.scratchAligned
  · exact endian.trans context.little
  · exact context.lengthBound

theorem recordPrice_mono (length maximum : Nat) (bound : length≤maximum) : recordPrice length≤recordPrice maximum := by
  unfold recordPrice Keccak256.price
  omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Environment.of_control
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.HashContext.of_control
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.recordPrice_mono
