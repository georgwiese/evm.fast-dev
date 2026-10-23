import InitECandidate.Solver.Mpt.FromWitnessNormal
import InitECandidate.Solver.Mpt.FromWitnessCost
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.FromWitness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors

/-- Actual scoped original245 callers receive the newly established map,
its complete physical graph and database frame, with their other locals
restored. The db boundary names the actual argument, not a caller local. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (input : Guest.InputBlob)
    (db incoming rootHash flag emptyRoot : BitVec 64)
    (boundary : RootBoundary input (bind source "db" db))
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values db rootHash flag))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word incoming))) (heapLower : 2713731432≤incoming.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "mpt_from_witness") arguments) target) :
    ∃ map : BitVec 64,target.locals.lookup name=some (.val (.word map)) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Nonempty (Output input source target (.val (.word map)) db incoming flag) := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=values db rootHash flag:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,dbCell,rootCell,flagCell⟩:=environment source.code.lookup db rootHash flag (original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=body at bodyEq
    change callee=expected at mapEq
    change actualShape=.one at shapeEq
    subst actualBody
    subst callee
    subst actualShape
    let entry:=callEntryStateHOLFinite source expected
    have entryBoundary:=boundary.erase_frame input (bind source "db" db) entry rfl (dbCell.trans (bind_lookup_same source "db" db).symm)
    have entryScratch:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
    obtain ⟨output⟩:=body_normal input entry childTarget db incoming rootHash flag emptyRoot entryBoundary little installed dbCell rootCell flagCell emptyCell heapCell heapLower entryScratch returned run
    have frozen:=output.frozen.frame input (bind childTarget "db" db) (bind (setVarHOLFinite name returned {childTarget with locals:=source.locals}) "db" db) incoming.toNat rfl rfl
      ((bind_lookup_same _ "db" db).trans (bind_lookup_same childTarget "db" db).symm) (by intros; rfl)
    refine ⟨output.map,?_,?_,⟨{output with answer:=rfl,frozen:=frozen,header:=output.header.of_erase childTarget (setVarHOLFinite name returned {childTarget with locals:=source.locals}) output.graph output.graph output.map output.root flag rfl rfl}⟩⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,output.answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

/-- Current actual arguments determine a whole original245 call allowance
for every outcome, including failed child calls and clock exhaustion. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (db root flag : BitVec 64) (boundary : RootBoundary input (bind source "db" db))
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (hash : Keccak256.Environment source 2713714976#64 2713715176#64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values db root flag)) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "mpt_from_witness") arguments)).2.clock≤rootDecoderPrice input+5 := by
  obtain ⟨callee,called,dbCell,rootCell,_flagCell⟩:=environment source.code.lookup db root flag (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input (bind source "db" db) entry rfl (dbCell.trans (bind_lookup_same source "db" db).symm)
  have entryScratch:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
  have entryHash:=hash.of_fields source entry 2713714976#64 2713715176#64 rfl rfl rfl (HeapGlobals.refl source)
  have price:=body_cost input entry db root entryBoundary installed scalars dbCell rootCell entryScratch entryHash
  exact Input.ClockCost.call_current source destination (ofString "mpt_from_witness") arguments _ body callee .one (rootDecoderPrice input+4) args called price

end InitECandidate.Solver.Mpt.FromWitness

#print axioms InitECandidate.Solver.Mpt.FromWitness.scoped_normal
#print axioms InitECandidate.Solver.Mpt.FromWitness.call_cost
