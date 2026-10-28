import InitECandidate.Solver.Input.CurrentTable.NodeBuild.StateTransport
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopReads
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.HashImage

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The same actual hash return retains the current insertion history,
all decoded rows, caller bindings and the original persistent heap. -/
theorem hash_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total)
    (run : evaluateHOLFiniteState source hashCall=(none,post)) : State data origin post index := by
  unfold hashCall at run
  have args := hash_arguments data origin source index state inside
  have fields := evaluation_fields source post hashCall none run
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key := by
    have frame := CurrentKeccak.Hash.call_globals key source.code state.arena.code hashArguments source rfl
    rw [run] at frame
    exact congrArg Prod.snd frame
  have locals (key : MlS) : post.locals.lookup key=source.locals.lookup key :=
    CallNormal.ignored_lookup source post key (ofString "keccak256") hashArguments run
  have input : HashInput.Frame source post data.lower data.upper := by
    refine ⟨?_⟩
    intro query lower upper
    exact (CurrentKeccak.Hash.call_frame source post data.stp data.pad (data.pointers index) data.out query (data.lengths index).toNat
      state.environment hashArguments args (state.rows.inputArena index inside) layout.outArena
      (CopyGeneral.Away.before data.stp query 200 data.lower layout.stateBefore layout.lowerSmall lower)
      (CopyGeneral.Away.before data.pad query 136 data.lower layout.padBefore layout.lowerSmall lower)
      (CopyGeneral.Away.before data.out query 32 data.lower layout.outBefore layout.lowerSmall lower) run).memory
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := state.image
  have nextImage := hash_image source post data.table data.cap root (data.pointers index) data.out data.stp data.pad (data.lengths index).toNat
    next count valid bits left right keys (ValueOf data) image state.environment hashArguments args (state.rows.inputArena index inside) layout.outArena
    (by have a:=layout.stateBefore; have b:=layout.lowerUpper; have c:=layout.inputBefore; omega)
    (by have a:=layout.padBefore; have b:=layout.lowerUpper; have c:=layout.inputBefore; omega)
    (by have a:=layout.outBefore; have b:=layout.lowerUpper; have c:=layout.inputBefore; omega) run
  exact state.transport data origin source post index index fields.2.2.2 fields.1 fields.2.1 globals (fun key _=>locals key)
    input ((locals _).trans state.indexCell) ⟨root,next,count,valid,bits,left,right,keys,nextImage,bound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.hash_normal
