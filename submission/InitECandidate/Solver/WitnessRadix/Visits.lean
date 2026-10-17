import InitECandidate.Solver.WitnessRadix.Space

namespace InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

/-- Conservative record-pass accounting for the proposed iterative code:
count zero bits, stable-scatter, then copy the partition back. At a terminal
bucket one last-record selection pass is allowed. This intentionally charges
all three passes even for unary levels where the implementation skips two. -/
def arrayPassVisits (bit : Key → Nat → Bool) (position : Nat) :
    Nat → List (Key × Value) → Nat
  | 0, input => input.length
  | fuel + 1, input =>
      3 * input.length +
        arrayPassVisits bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position) +
        arrayPassVisits bit (position + 1) fuel (input.filter fun entry => bit entry.1 position)

theorem arrayPassVisits_bound (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) :
    arrayPassVisits bit position fuel input ≤ (3 * fuel + 1) * input.length := by
  induction fuel generalizing position input with
  | zero => simp [arrayPassVisits]
  | succ fuel ih =>
      rw [arrayPassVisits]
      have left := ih (position + 1) (input.filter fun e => !bit e.1 position)
      have right := ih (position + 1) (input.filter fun e => bit e.1 position)
      have total := filter_length_sum (fun e => bit e.1 position) input
      have paid : (3 * fuel + 1) * (input.filter fun e => !bit e.1 position).length +
          (3 * fuel + 1) * (input.filter fun e => bit e.1 position).length =
          (3 * fuel + 1) * input.length := by rw [← Nat.mul_add, total]
      have expand : (3 * (fuel + 1) + 1) * input.length =
          3 * input.length + (3 * fuel + 1) * input.length := by
        rw [show 3 * (fuel + 1) + 1 = 3 + (3 * fuel + 1) by omega, Nat.add_mul]
      omega

def queryTotal (bit : Key → Nat → Bool) (index : CompactIndex Key Value) : List Key → Nat
  | [] => 0
  | key :: rest => queryVisits bit key index + queryTotal bit index rest

theorem queryTotal_buildIndex (bit : Key → Nat → Bool) (width : Nat)
    (input : List (Key × Value)) (queries : List Key) :
    queryTotal bit (buildIndex bit width input) queries ≤ (width + 1) * queries.length := by
  induction queries with
  | nil => simp [queryTotal]
  | cons key rest ih =>
      have step := queryVisits_buildIndex bit width input key
      simp only [queryTotal, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem hash_array_passes (input : List (BitVec 256 × Value)) :
    arrayPassVisits BitVec.getLsbD 0 256 input ≤ 769 * input.length :=
  arrayPassVisits_bound BitVec.getLsbD 0 256 input

theorem hash_query_total (input : List (BitVec 256 × Value)) (queries : List (BitVec 256)) :
    queryTotal BitVec.getLsbD (buildIndex BitVec.getLsbD 256 input) queries ≤ 257 * queries.length :=
  queryTotal_buildIndex BitVec.getLsbD 256 input queries

/-- The input-envelope arithmetic is conditional: decoder/input correspondence
must establish the record-count premise for the actual challenge execution. -/
theorem hash_array_input_envelope (input : List (BitVec 256 × Value))
    (records : input.length ≤ 33554428) :
    arrayPassVisits BitVec.getLsbD 0 256 input ≤ 25803355132 := by
  have counted := hash_array_passes input
  omega

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.hash_array_passes
#print axioms InitECandidate.Solver.WitnessRadix.hash_query_total
#print axioms InitECandidate.Solver.WitnessRadix.hash_array_input_envelope
