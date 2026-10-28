import InitECandidate.Solver.Input.CurrentHash.RequestListProgram
import InitECandidate.Solver.Input.CurrentHash.FixedRecordCost
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  category : source.locals.lookup (ofString "kind")=some (.val (.word (BitVec.ofNat 64 kind.tag)))
  pointer : source.locals.lookup (ofString "p")=some (.val (.word p))
  count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))
  size : source.locals.lookup (ofString "sz")=some (.val (.word (BitVec.ofNat 64 kind.record.length)))
  root : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out n index) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (FixedRecord.scalarValues (p+BitVec.ofNat 64 (index*kind.record.length)) (roots+BitVec.ofNat 64 (32*index))) := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,actual.pointer,actual.position,actual.size,actual.root,
    FixedRecord.scalarValues,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

/-- The selected real record call has its fixed current price. On normal
continuation, caller bindings are restored regardless of memory/heap effects. -/
theorem call_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n index : Nat)
    (actual : RoundState source kind p roots out n index)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.call (some (none,none)) kind.record.name arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤kind.record.price+1 ∧ (result=none → RoundState post kind p roots out n index) := by
  have args := arguments_read source kind p roots out n index actual
  have price := FixedRecord.call_cost kind.record source post (p+BitVec.ofNat 64 (index*kind.record.length))
    (roots+BitVec.ofNat 64 (32*index)) actual.installed (some none) arguments args result run notTimeout
  refine ⟨price,?_⟩
  intro normal
  subst result
  have nextCode : OriginalCode.Installed post.code := by
    rw [(evaluation_fields source post _ none run).2.2.2]
    exact actual.installed
  have other (name : String) := CallNormal.ignored_lookup source post (ofString name) kind.record.name arguments run
  exact ⟨nextCode,(other "kind").trans actual.category,(other "p").trans actual.pointer,(other "n").trans actual.count,(other "sz").trans actual.size,
    (other "roots").trans actual.root,(other "out").trans actual.output,(other "i").trans actual.position⟩

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.call_summary
