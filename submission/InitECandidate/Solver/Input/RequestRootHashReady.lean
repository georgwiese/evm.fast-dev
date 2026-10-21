import InitECandidate.Solver.Input.RequestRootHashGeometry

namespace InitECandidate.Solver.Input.RequestRootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Ready (data : Description) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) : Prop where
  workspace : SszHash.Workspace current stp accel chunk zeros
  si : current.locals.lookup (ofString "si")=some (.val (.word data.si))
  chunks : current.locals.lookup (ofString "ch")=some (.val (.word ch))
  output : current.locals.lookup (ofString "out")=some (.val (.word out))
  saved : current.locals.lookup (ofString "mark")=some (.val (.word mark))
  heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor ch)))
  input : HashInput.Frame origin current lower upper

def Phase.values (phase : Phase) (data : Description) (ch out : BitVec 64) : List (ValueHOL 64) := match phase with
  | .payload=>PayloadHash.values data.payload.payload ch
  | .blobs=>PListChunks.values data.blobs data.blobCount (BitVec.ofNat 64 data.blobCount) (ch+32#64)
  | .parent=>CopyGeneral.values (ch+64#64) data.parent 32
  | .requests=>RequestsHash.values data.requests (ch+96#64)
  | .root=>Merkle.values ch 4#64 4#64 out

def Phase.price (phase : Phase) (data : Description) : Nat := match phase with
  | .payload=>PayloadHash.bodyPrice data.payload+1
  | .blobs=>115*data.blobCount+24207
  | .parent=>5
  | .requests=>RequestsHash.price data.requestCount+1
  | .root=>584

theorem output_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) (slot : Nat) :
    eval source (outputExpression slot)=some (.val (.word (ch+BitVec.ofNat 64 (32*slot)))) := by
  by_cases zero : slot=0
  · subst slot; simp [outputExpression,eval,evalHOLExact,toExact,localVar,chunks]
  · simp [outputExpression,zero,eval,evalHOLExact,evalListHOLExact,toExact,localVar,chunks,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Every literal phase argument is read from the actual preserved SI
cells and current caller locals, independently of previous digest values. -/
theorem arguments_read (phase : Phase) (data : Description) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper budget : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (image : data.Image origin) (layout : data.Layout lower upper budget)
    (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) phase.arguments=some (phase.values data ch out) := by
  have p0 := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.si (0,data.payload.payload) (by simp [Description.cells])
  have p8 := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.si (8,data.blobs) (by simp [Description.cells])
  have p16 := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.si (16,BitVec.ofNat 64 data.blobCount) (by simp [Description.cells])
  have p24 := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.si (24,data.parent) (by simp [Description.cells])
  have p32 := data.field_read origin source lower upper budget image layout actual.input actual.workspace.sha.domain actual.si (32,data.requests) (by simp [Description.cells])
  have o1 := output_read source ch actual.chunks 1
  have o2 := output_read source ch actual.chunks 2
  have o3 := output_read source ch actual.chunks 3
  simp only [eval] at p0 p8 p16 p24 p32 o1 o2 o3
  cases phase <;> simp only [Phase.arguments,evalListHOLFinite,evalListHOLExact,p0,p8,p16,p24,p32,o1,o2,o3,Phase.values,
    PayloadHash.values,PListChunks.values,CopyGeneral.values,RequestsHash.values,Merkle.values,evalHOLExact,toExact,localVar,actual.chunks,actual.output]

/-- Same actual ignored normal phase retains the caller bindings and
workspace once its real heap and memory frames have been established. -/
theorem Ready.after_call (data : Description) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat)
    (ch out mark stp accel chunk zeros : BitVec 64) (actual : Ready data origin source lower upper ch out mark stp accel chunk zeros)
    (phase : Phase) (run : evaluateHOLFiniteState source phase.call=(none,post))
    (heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor ch))))
    (effects : ∀ key,key≠ofString "heap_ptr" → GlobalEffects.Preserves key source.code phase.call)
    (frame : HashInput.Frame origin post lower upper) : Ready data origin post lower upper ch out mark stp accel chunk zeros := by
  exact ⟨actual.workspace.after source post stp accel chunk zeros phase.call none run effects,
    (CallNormal.ignored_lookup source post (ofString "si") phase.function phase.arguments run).trans actual.si,
    (CallNormal.ignored_lookup source post (ofString "ch") phase.function phase.arguments run).trans actual.chunks,
    (CallNormal.ignored_lookup source post (ofString "out") phase.function phase.arguments run).trans actual.output,
    (CallNormal.ignored_lookup source post (ofString "mark") phase.function phase.arguments run).trans actual.saved,heap,frame⟩

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.output_read
#print axioms InitECandidate.Solver.Input.RequestRootHash.arguments_read
#print axioms InitECandidate.Solver.Input.RequestRootHash.Ready.after_call
