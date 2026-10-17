import Guest.Model
import InitECandidate.Solver.WitnessRadix.RawProgram
import InitECandidate.Solver.WitnessRadix.Compact

/-! Executable regression check of the proposed Pancake radix builder under
the optional stepped evaluator. This is NOT a HOL/target refinement theorem. -/
open Flapjack Guest
open InitECandidate.Solver.WitnessRadix

abbrev TestMemory := Guest.Memory

def tab : Nat := 4096
def keyBase : Nat := 8192
def valBase : Nat := 65536
def srcBase : Nat := 131072
def dstBase : Nat := 196608
def recordBase : Nat := 262144

def testStoreWord (memory : TestMemory) (address value : Nat) : TestMemory :=
  fun a => if a = BitVec.ofNat 64 address then some (.word (BitVec.ofNat 64 value)) else memory a

def testReadWord (memory : TestMemory) (address : Nat) : Option Nat :=
  match memory (BitVec.ofNat 64 address) with
  | some (.word value) => some value.toNat
  | _ => none

def memoryFor (keys : List (BitVec 256)) : TestMemory := Id.run do
  let mut memory : TestMemory := fun a =>
    if a.toNat % 8 = 0 && a.toNat < 1048576 then some (.word 0) else none
  for (offset, value) in [(16, 1024), (24, 0), (32, keyBase), (40, valBase),
      (48, 98304), (56, srcBase), (64, dstBase)] do
    memory := testStoreWord memory (tab + offset) value
  for (key, i) in keys.zipIdx do
    for limb in List.range 4 do
      memory := testStoreWord memory (keyBase + 32 * i + 8 * limb)
        (key.toNat / 2 ^ (64 * limb))
    memory := testStoreWord memory (valBase + 8 * i) (recordBase + 16 * i)
    memory := testStoreWord memory (srcBase + 8 * i) i
  return memory

def builderProgram : List (Decl (BitVec 64)) :=
  [RawProgram.guestFn_solver_radix_index]

def runBuilder (keys : List (BitVec 256)) : Option (TestMemory × Nat) := do
  let result ← evalPanValueFfiProgramStepped guestFfiContext
    { source := { guestInitialState with memory := memoryFor keys }, ffi := guestFfiState [] }
    guestPrimitiveHandler guestHostFfi 10000 builderProgram "solver_radix_index"
    [.const (BitVec.ofNat 64 tab), .const (BitVec.ofNat 64 keys.length)]
    (memoryAccess := some guestMemoryAccess)
  match result.1 with
  | .returned _ _ memory _ [.word value] =>
      if value = 0 then some (memory, result.2) else none
  | _ => none

def readKey (memory : TestMemory) (ordinal : Nat) : Option (BitVec 256) := do
  let mut value := 0
  for limb in List.range 4 do
    let word ← testReadWord memory (keyBase + ordinal * 32 + limb * 8)
    value := value + word * 2 ^ (64 * limb)
  return BitVec.ofNat 256 value

def memoryLookup (memory : TestMemory) (records : Nat) (key : BitVec 256) :
    Nat → Nat → Option (Option Nat × Nat)
  | 0, _ => none
  | fuel + 1, node => do
      if node = 0 then return (none, 1)
      if node % 2 = 1 then
        let ordinal := node / 2
        if ordinal ≥ records then none else do
          let stored ← readKey memory ordinal
          if stored = key then return (some ordinal, 1) else return (none, 1)
      else
        if node < keyBase + records * 32 || keyBase + records * 56 ≤ node || node % 8 != 0 then
          none
        else do
          let position ← testReadWord memory node
          if position ≥ 256 then none else do
            let child ← testReadWord memory (node + if key.getLsbD position then 16 else 8)
            let result ← memoryLookup memory records key fuel child
            return (result.1, result.2 + 1)

def testCase (name : String) (keys : List (BitVec 256)) : IO Unit := do
  IO.eprintln s!"START {name}"
  (← IO.getStderr).flush
  let some (memory, steps) := runBuilder keys
    | throw (IO.userError s!"{name}: Pancake builder did not return")
  let some root := testReadWord memory (tab + 24)
    | throw (IO.userError s!"{name}: root missing")
  let queries := keys ++ [0, 1, 2, 3, BitVec.ofNat 256 (2 ^ 128), BitVec.ofNat 256 (2 ^ 255), BitVec.ofNat 256 (2 ^ 256 - 1)]
  let entries := keys.zipIdx
  let mut maximum := 0
  for key in queries do
    let some (value, visits) := memoryLookup memory keys.length key 257 root
      | throw (IO.userError s!"{name}: invalid index/query depth")
    let expected := lastValue key entries
    unless value = expected do
      throw (IO.userError s!"{name}: lookup mismatch at {key.toNat}: {repr value} vs {repr expected}")
    maximum := max maximum visits
  for i in List.range keys.length do
    unless readKey memory i = some keys[i]! do
      throw (IO.userError s!"{name}: immutable key row corrupted")
    unless testReadWord memory (valBase + 8 * i) = some (recordBase + 16 * i) do
      throw (IO.userError s!"{name}: immutable value row corrupted")
  IO.println s!"PASS {name}: N={keys.length}, stepped Pancake steps={steps}, max query nodes={maximum}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let cases : List (String × List (BitVec 256)) := [
    ("empty", []),
    ("singleton", [7]),
    ("last-bit split", [0, BitVec.ofNat 256 (2 ^ 255)]),
    ("all equal", List.replicate 12 123456),
    ("duplicates", [3, 0, 1, 3, 2, 0, 1, 2, 3, 0]),
    ("reversed byte keys", (List.range 32).reverse.map (BitVec.ofNat 256)),
    ("long-common-prefix", (List.range 24).map fun i => BitVec.ofNat 256 (i * 2 ^ 248)),
    ("mixed bits", (List.range 40).map fun i =>
      BitVec.ofNat 256 ((i * 7919 + 17) * 2 ^ 128 + (i % 11) * 2 ^ 64 + i % 7))]
  for (name, keys) in cases do
    if args.isEmpty || args.contains name then testCase name keys
