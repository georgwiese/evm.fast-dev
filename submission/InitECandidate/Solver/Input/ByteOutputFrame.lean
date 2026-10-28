import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.MemoryContinue

namespace InitECandidate.Solver.Input.ByteOutputFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Recognize a literal byte displacement from a stable local output pointer. -/
def offset? (key : MlS) : ExpHOL 64 → Option (BitVec 64)
  | .var .local name => if name = key then some 0#64 else none
  | .op .add [.var .local name, .const offset] => if name = key then some offset else none
  | _ => none

theorem offset_sound (key : MlS) (expression : ExpHOL 64) (offset : BitVec 64)
    (checked : offset? key expression = some offset)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (cell : source.locals.lookup key = some (.val (.word pointer))) :
    eval source expression = some (.val (.word (pointer+offset))) := by
  unfold offset? at checked
  split at checked
  · rename_i name
    split at checked
    · cases checked
      subst name
      simp [eval,evalHOLExact,toExact,cell]
    · cases checked
  · rename_i name displacement
    split at checked
    · cases checked
      subst name
      simp [eval,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
    · cases checked
  · cases checked

/-- A finite straight body writes only its output bytes and never rebinds the
tracked output pointer. No successful read or stored digest value is assumed. -/
def accepts (key : MlS) (size : Nat) : ProgHOL 64 → Bool
  | .skip | .return _ => true
  | .assign .local name _ => decide (name ≠ key)
  | .storeByte address _ => match offset? key address with
    | some offset => decide (offset.toNat < size)
    | none => false
  | .seq first second => accepts key size first && accepts key size second
  | .dec name _ _ body => decide (name ≠ key) && accepts key size body
  | _ => false

def Frame (key : MlS) (pointer query : BitVec 64) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
    source.locals.lookup key = some (.val (.word pointer)) →
    (evaluateHOLFiniteState source program).2.memory query = source.memory query ∧
    ((evaluateHOLFiniteState source program).1 = none →
      (evaluateHOLFiniteState source program).2.locals.lookup key = some (.val (.word pointer)))

private theorem restore_other (map : HolFiniteMapExact MlS (ValueHOL 64))
    (key name : MlS) (value : Option (ValueHOL 64)) (other : name ≠ key) :
    (HolFiniteMapExact.resVarEq map (name, value)).lookup key = map.lookup key := by
  rw [lookup_resVarEq_toExact]
  cases value <;> simp [resVarHOLExact, FUPDATE, other, Ne.symm other]

theorem sequence (key : MlS) (pointer query : BitVec 64) (first second : ProgHOL 64)
    (front : Frame key pointer query first) (back : Frame key pointer query second) :
    Frame key pointer query (.seq first second) := by
  intro source cell
  have firstFrame := front source cell
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstFrame ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have next := back middle (firstFrame.2 rfl)
    exact ⟨next.1.trans firstFrame.1, next.2⟩
  | some result => exact ⟨firstFrame.1, by simp⟩

theorem declared (key name : MlS) (pointer query : BitVec 64) (shape : ShapeHOL)
    (expression : ExpHOL 64) (body : ProgHOL 64) (other : name ≠ key)
    (bodyFrame : Frame key pointer query body) : Frame key pointer query (.dec name shape expression body) := by
  intro source cell
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · exact ⟨rfl, by simp⟩
  · rename_i value read
    split
    · have nextCell : (setVarHOLFinite name value source).locals.lookup key = some (.val (.word pointer)) :=
        (MemoryAt.set_lookup_other source name key value other).trans cell
      have next := bodyFrame (setVarHOLFinite name value source) nextCell
      refine ⟨next.1, ?_⟩
      intro normal
      rw [restore_other _ key name _ other]
      exact next.2 normal
    · exact ⟨rfl, by simp⟩

/-- Kernel-checked syntax soundness: all actual outcomes preserve every memory
word outside the output's byte backing words. -/
theorem sound (key : MlS) (size : Nat) (program : ProgHOL 64)
    (checked : accepts key size program = true) (pointer query : BitVec 64)
    (away : ∀ offset : Nat, offset < size → query ≠ panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset)) :
    Frame key pointer query program := by
  cases program with
  | skip => intro source cell; rw [evaluateHOLFiniteState_skip]; exact ⟨rfl, fun _ => cell⟩
  | «return» expression =>
    intro source cell
    rw [evaluateHOLFiniteState_return]
    repeat first | exact ⟨rfl, by simp⟩ | split
  | assign kind name expression =>
    cases kind with
    | «global» => cases checked
    | «local» =>
      have other : name ≠ key := of_decide_eq_true checked
      intro source cell
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨rfl, by simp⟩
      · split
        · exact ⟨rfl, fun _ => (MemoryAt.set_lookup_other source name key _ other).trans cell⟩
        · exact ⟨rfl, by simp⟩
  | storeByte address value =>
    unfold accepts at checked
    cases found : offset? key address with
    | none => simp only [found] at checked; cases checked
    | some offset =>
      have inside : offset.toNat < size := of_decide_eq_true (by simpa only [found] using checked)
      intro source cell
      have read := offset_sound key address offset found source pointer cell
      have outside : query ≠ panByteAlignHOL (width := 64) (pointer + offset) := by
        simpa using away offset.toNat inside
      refine ⟨MemoryAt.byte_store_current source _ value (pointer + offset) query read outside, ?_⟩
      have locals : (evaluateHOLFiniteState source (.storeByte address value)).2.locals = source.locals := by
        rw [evaluateHOLFiniteState_storeByte]
        repeat first | rfl | split
      intro normal
      rw [locals]
      exact cell
  | seq first second =>
    have parts : accepts key size first = true ∧ accepts key size second = true := by
      simpa only [accepts, Bool.and_eq_true] using checked
    exact sequence key pointer query first second (sound key size first parts.1 pointer query away)
      (sound key size second parts.2 pointer query away)
  | dec name shape expression body =>
    have parts : name ≠ key ∧ accepts key size body = true := by
      simpa only [accepts, Bool.and_eq_true, decide_eq_true_eq] using checked
    exact declared key name pointer query shape expression body parts.1 (sound key size body parts.2 pointer query away)
  | _ => simp only [accepts] at checked; cases checked
termination_by structural program

end InitECandidate.Solver.Input.ByteOutputFrame

#print axioms InitECandidate.Solver.Input.ByteOutputFrame.offset_sound
#print axioms InitECandidate.Solver.Input.ByteOutputFrame.sequence
#print axioms InitECandidate.Solver.Input.ByteOutputFrame.declared
#print axioms InitECandidate.Solver.Input.ByteOutputFrame.sound
