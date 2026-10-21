import InitECandidate.Solver.Input.RequestListHashProgram

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat) : Prop where
  workspace : SszHash.Workspace source stp accel chunk zeros
  category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag)))
  pointer : source.locals.lookup (ofString "p")=some (.val (.word p))
  count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))
  size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length)))
  root : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))

structure Geometry (kind : Kind) (p roots cursor : BitVec 64) (n : Nat) : Prop where
  inputArena : AllocatedBytes.Arena p (n*kind.record.length)
  rootsArena : AllocatedBytes.Arena roots (32*n)
  rootsAligned : roots.toNat%8=0
  arena : AllocatedBytes.Arena cursor 1280
  aligned : cursor.toNat%8=0

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (FixedHash.values (p+BitVec.ofNat 64 (index*kind.record.length)) (roots+BitVec.ofNat 64 (32*index))) := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,actual.pointer,actual.position,actual.size,actual.root,
    FixedHash.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem iteration_geometry (kind : Kind) (p roots cursor : BitVec 64) (n index : Nat) (active : index<n) (geometry : Geometry kind p roots cursor n) :
    AllocatedBytes.Arena (p+BitVec.ofNat 64 (index*kind.record.length)) kind.record.length ∧
    AllocatedBytes.Arena (roots+BitVec.ofNat 64 (32*index)) 32 ∧ (roots+BitVec.ofNat 64 (32*index)).toNat%8=0 ∧
    AllocatedBytes.Arena cursor (32*kind.record.count+1120) := by
  have inputBound : index*kind.record.length+kind.record.length≤n*kind.record.length := by
    have h := Nat.mul_le_mul_right kind.record.length (show index+1≤n by omega)
    simpa only [Nat.add_mul,Nat.one_mul] using h
  have outputBound : 32*index+32≤32*n := by omega
  have number : (roots+BitVec.ofNat 64 (32*index)).toNat=roots.toNat+32*index := byteAddress_toNat roots (32*index) (by have h:=geometry.rootsArena.upper; omega)
  refine ⟨AllocatedBytes.Arena.subrange p (n*kind.record.length) (index*kind.record.length) kind.record.length geometry.inputArena inputBound,
    AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 geometry.rootsArena outputBound,by rw [number]; have h:=geometry.rootsAligned; omega,?_⟩
  exact AllocatedBytes.Arena.weaken cursor 1280 _ geometry.arena (by have h:=(FixedHash.count_bounds kind.record).2.1; omega)

/-- One actual selected original record hash, at the loop's real input and
output slot. Normal return retains the current round state and heap. -/
theorem call_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (active : index<n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (some (none,none)) kind.record.name arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤kind.record.price+1 ∧ (result=none → RoundState post kind p roots out cursor stp accel chunk zeros n index) := by
  obtain ⟨inputArena,outArena,outAligned,temporary⟩ := iteration_geometry kind p roots cursor n index active geometry
  have args := arguments_read source kind p roots out cursor stp accel chunk zeros n index actual
  have price := FixedHash.call_cost kind.record source post (p+BitVec.ofNat 64 (index*kind.record.length)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros actual.workspace actual.heap
    inputArena temporary geometry.aligned outArena (some none) arguments args result run notTimeout
  refine ⟨price,?_⟩
  intro normal
  subst result
  have heap := FixedHash.ignored_return_heap kind.record source post (p+BitVec.ofNat 64 (index*kind.record.length)) cursor (roots+BitVec.ofNat 64 (32*index)) stp accel chunk zeros actual.workspace actual.heap
    inputArena temporary geometry.aligned outArena arguments args run
  have nextWorkspace := SszHash.Workspace.after source post stp accel chunk zeros actual.workspace _ none run
    (fun key different=>GlobalEffects.call_body key source.code (some none) kind.record.name arguments kind.record.formals kind.record.body .one
      (FixedHash.original_code kind.record source.code actual.workspace.sha.installed) (FixedHash.globals kind.record key source.code actual.workspace.sha.installed different))
  have other (name : String) := CallNormal.ignored_lookup source post (ofString name) kind.record.name arguments run
  exact ⟨nextWorkspace,(other "kind").trans actual.category,(other "p").trans actual.pointer,(other "n").trans actual.count,(other "sz").trans actual.size,
    (other "roots").trans actual.root,(other "out").trans actual.output,(other "i").trans actual.position,heap⟩

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.arguments_read
#print axioms InitECandidate.Solver.Input.RequestListHash.iteration_geometry
#print axioms InitECandidate.Solver.Input.RequestListHash.call_summary
