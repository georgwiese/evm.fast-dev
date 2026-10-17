import InitECandidate.Solver.WitnessRadix.ConstructorTablePopulate
import InitECandidate.Solver.WitnessRadix.CapacityEntry

namespace InitECandidate.Solver.WitnessRadix.Constructor

def padding (capacity : Nat) : Nat := if capacity=4 then 4 else 0
def allocationPlan (records table count capacity : Nat) : AllocatedLayout.Plan :=
  ⟨table,records,count,capacity,padding capacity⟩

theorem padding_bound (capacity : Nat) : padding capacity<8 := by unfold padding; split <;> omega

theorem allocation_ready (records table count capacity : Nat)
    (recordsLower : 2701131776≤records) (recordsBefore : records+16*count≤table)
    (recordsAligned : records%8=0) (tableAligned : table%8=0)
    (room : table+72+57*(4*count+4)+7≤33806089496)
    (sufficient : 2*count+2≤capacity) (capBound : capacity≤4*count+4) (shape : capacity=4 ∨ capacity%8=0) :
    AllocatedLayout.Ready (allocationPlan records table count capacity) := by
  have padded : (capacity+padding capacity)%8=0 := by
    rcases shape with four|multiple
    · simp [padding,four]
    · by_cases four : capacity=4
      · simp [padding,four]
      · simp [padding,four,multiple]
  exact ⟨sufficient,tableAligned,recordsAligned,padded,padding_bound capacity,recordsLower,recordsBefore,
    by change table+72+57*capacity+padding capacity≤33806089496; have := padding_bound capacity; omega⟩

theorem table_price_bound (capacity : Nat) : TableNew.price capacity≤capacity+11 := by
  unfold TableNew.price TableNew.clearCost
  split
  · omega
  · unfold Zero.price
    omega

def wholePrice (maximum count : Nat) : Nat := populatePrice maximum count+4*count+46

theorem table_populate_price_bound (maximum records table count capacity : Nat) (capBound : capacity≤4*count+4) :
    tablePopulatePrice maximum (allocationPlan records table count capacity)+30≤wholePrice maximum count := by
  have h := table_price_bound capacity
  unfold tablePopulatePrice wholePrice
  change TableNew.price capacity+1+populatePrice maximum count+30≤populatePrice maximum count+4*count+46
  omega

theorem wholePrice_nodes (count : Nat) : wholePrice 1024 count=1378*count+47 := by
  rw [wholePrice,populatePrice_nodes]
  omega

theorem wholePrice_code (count : Nat) : wholePrice 65536 count=10858*count+47 := by
  rw [wholePrice,populatePrice_code]
  omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.allocation_ready
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.table_price_bound
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.table_populate_price_bound
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.wholePrice_nodes
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.wholePrice_code
