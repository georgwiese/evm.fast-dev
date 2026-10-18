import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An all-outcome upper bound on source call/loop clocks actually spent.
Straight-line target work must still be counted separately. -/
def Bound (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (program : ProgHOL 64) (price : Nat) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    source.clock - (evaluateHOLFiniteState source program).2.clock ≤ price

theorem of_quiet (code) (program : ProgHOL 64) (quiet : QuietClock.Preserves code program) : Bound code program 0 := by
  intro source installed
  rw [quiet source installed]
  omega

theorem mono (code) (program : ProgHOL 64) (small large : Nat) (priced : Bound code program small) (bounded : small ≤ large) :
    Bound code program large := by
  intro source installed
  exact (priced source installed).trans bounded

theorem skip (code) : Bound code .skip 0 := of_quiet code _ (QuietClock.skip code)
theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Bound code (.assign .local name expression) 0 := of_quiet code _ (QuietClock.assign code name expression)
theorem primitive (code) (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) : Bound code (.primitive name operator arguments) 0 := of_quiet code _ (QuietClock.primitive code name operator arguments)
theorem returned (code) (expression : ExpHOL 64) : Bound code (.return expression) 0 := of_quiet code _ (QuietClock.returned code expression)
theorem raised (code) (name : MlS) (expression : ExpHOL 64) : Bound code (.raise name expression) 0 := of_quiet code _ (QuietClock.raised code name expression)
theorem store (code) (address value : ExpHOL 64) : Bound code (.store address value) 0 := of_quiet code _ (QuietClock.store code address value)
theorem stopped (code) : Bound code .break 0 ∧ Bound code .continue 0 :=
  ⟨of_quiet code _ (QuietClock.stopped code).1, of_quiet code _ (QuietClock.stopped code).2⟩

theorem sequence (code) (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (front : Bound code first firstPrice) (back : Bound code second secondPrice) : Bound code (.seq first second) (firstPrice + secondPrice) := by
  intro source installed
  have firstCost := front source installed
  have firstClock := evaluateHOLFiniteState_clock_le source first
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstCost firstClock ⊢
  obtain ⟨result, middle⟩ := output
  change source.clock - middle.clock ≤ firstPrice at firstCost
  change middle.clock ≤ source.clock at firstClock
  cases result with
  | none =>
    change source.clock - (evaluateHOLFiniteState middle second).2.clock ≤ firstPrice + secondPrice
    have codeEq := (Input.evaluation_fields source middle first none computed).2.2.2
    have secondCost := back middle (codeEq.trans installed)
    have secondClock := evaluateHOLFiniteState_clock_le middle second
    omega
  | some result =>
    change source.clock - middle.clock ≤ firstPrice + secondPrice
    omega

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (yesPrice noPrice : Nat)
    (left : Bound code yes yesPrice) (right : Bound code no noPrice) : Bound code (.ite test yes no) (max yesPrice noPrice) := by
  intro source installed
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = value
  cases value with
  | none => simp
  | some value =>
    cases value with
    | rStruct fields => simp
    | nStruct name fields => simp
    | val payload =>
      cases payload with
      | word word =>
        change source.clock - (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2.clock ≤ max yesPrice noPrice
        by_cases zero : word = 0
        · rw [if_pos zero]
          exact (right source installed).trans (Nat.le_max_right _ _)
        · rw [if_neg zero]
          exact (left source installed).trans (Nat.le_max_left _ _)

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (price : Nat)
    (priced : Bound code body price) : Bound code (.dec name shape expression body) price := by
  intro source installed
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i value read
    split
    · exact priced (setVarHOLFinite name value source) installed
    · simp

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.of_quiet
#print axioms InitECandidate.Solver.Input.ClockCost.mono
#print axioms InitECandidate.Solver.Input.ClockCost.sequence
#print axioms InitECandidate.Solver.Input.ClockCost.conditional
#print axioms InitECandidate.Solver.Input.ClockCost.declared
