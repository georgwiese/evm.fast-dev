import InitECandidate.Solver.Mpt.StateInitBlockState
import InitECandidate.Solver.MutableTable.WitnessBuildOriginalHelpers

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem capacity_bounds (kind : KeyHash.Kind) (bits : Nat) (lower : 3≤bits) (upper : bits≤8) :
    0<2^bits ∧ (2^bits)%8=0 ∧ stride kind*(2^bits)<2^64 ∧ 8*(2^bits)<2^64 ∧ 2^bits+32<2^64 := by
  have bounded : 2^bits≤256:=Nat.pow_le_pow_right (by decide) upper
  have factor : 2^bits=2^(bits-3)*8:=by
    rw [show bits=(bits-3)+3 from by omega,Nat.pow_add]
    rfl
  have strideBound : stride kind≤64:=by cases kind <;> decide
  have product:=Nat.mul_le_mul strideBound bounded
  exact ⟨Nat.pow_pos (by decide),by simp [factor,Nat.mul_mod],by omega,by omega,by omega⟩

/-- Invert one genuine original assigned constructor/field store, or
ancestor scalar store. The actual run derives constructor room and clock
funding and reaches the exact next state; no future helper is supplied. -/
theorem step_normal (action : Action) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (block start : Nat) (tail : Flapjack.Pancake.PanLang.ProgHOL 64) (oldT : BitVec 64)
    (validAction : action.Valid) (recordValid : MemoryRegion.Valid ⟨block,80⟩)
    (lower : 2701131776≤start) (bounded : start≤33806089496) (aligned : start%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 start))))
    (bs : source.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩))))
    (t : source.locals.lookup (ofString "t")=some (.val (.word oldT)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program [action] tail)=(some (.returned returned),post)) :
    StepLayout start action ∧ stepPrice action≤source.clock ∧ stepCursor start action≤33806089496 ∧
      stepCursor start action%8=0 ∧
      evaluateHOLFiniteState (stepState source block start action) tail=(some (.returned returned),post) := by
  cases action with
  | scalar offset value=>
    have actual:=Input.global_field_store source "bs" ⟨block,80⟩ recordValid domain offset validAction.1 validAction.2 bs (.const value) value rfl
    change evaluateHOLFiniteState source (fieldStore offset (.const value))=(none,writeField source block offset value) at actual
    rw [program,program,evaluateHOLFiniteState_seq_line780,actual] at normal
    exact ⟨True.intro,Nat.zero_le _,bounded,aligned,normal⟩
  | table kind bits offset=>
    obtain ⟨bitsLower,bitsUpper,offsetBound,offsetAligned⟩:=validAction
    obtain ⟨positive,multiple,keySmall,wordSmall,capSmall⟩:=capacity_bounds kind bits bitsLower bitsUpper
    have safe : Input.LocalPrefix (ofString "setup") (tableCall kind bits):=
      .call (some (ofString "t")) _ _ (by intro name equal; cases Option.some.inj equal; decide)
    rw [program,program] at normal
    obtain ⟨middle,called,continued,saved⟩:=safe.normal_continue source post (.seq (fieldStore offset (localVar "t")) tail) returned normal
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (tableArguments kind bits)=some (TableRuntime.values kind (2^bits)):=rfl
    have helpers:=WitnessBuild.original_helpers source.code installed
    obtain ⟨funded,valid,middleEq⟩:=TableRuntime.assigned_normal source middle kind start (2^bits) "t" (tableArguments kind bits) oldT positive lower bounded aligned
      keySmall wordSmall capSmall multiple domain args helpers.tableCode heap (PersistentAlloc.original_code source.code installed)
      (Input.Trap.original_code source.code installed) (Zero.original_code source.code installed) t called
    subst middle
    let entered:=TableRuntime.callState source "t" kind start (2^bits)
    have bsEntered : entered.globals.lookup (ofString "bs")=some (.val (.word (MemoryRegion.pointer ⟨block,80⟩))):=by
      simpa [entered,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "bs" from by decide] using bs
    have tEntered : entered.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 start))):=bind_lookup_same _ _ _
    have read : eval entered (localVar "t")=some (.val (.word (BitVec.ofNat 64 start))):=by simp [eval,localVar,evalHOLExact,toExact,tEntered]
    have actual:=Input.global_field_store entered "bs" ⟨block,80⟩ recordValid domain offset offsetBound offsetAligned bsEntered (localVar "t") (BitVec.ofNat 64 start) read
    change evaluateHOLFiniteState entered (fieldStore offset (localVar "t"))=(none,writeField entered block offset (BitVec.ofNat 64 start)) at actual
    change evaluateHOLFiniteState entered (.seq (fieldStore offset (localVar "t")) tail)=(some (.returned returned),post) at continued
    rw [evaluateHOLFiniteState_seq_line780,actual] at continued
    have nextBound : freshEnd kind start (2^bits)≤33806089496:=valid.upper .position
    have nextAligned : freshEnd kind start (2^bits)%8=0:=by
      have position:=valid.aligned .position
      change ((fresh kind start (2^bits)).base .position+8*(2^bits))%8=0
      rw [Nat.add_mod,position]
      omega
    exact ⟨valid,funded,nextBound,nextAligned,continued⟩

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.capacity_bounds
#print axioms InitECandidate.Solver.Mpt.StateInit.Block.step_normal
