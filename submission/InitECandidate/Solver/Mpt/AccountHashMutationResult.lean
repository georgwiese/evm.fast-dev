import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.MutableTable.FamilyValuePools
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame
import InitECandidate.Solver.WitnessRadix.Keccak256CurrentCall
import InitECandidate.Solver.WitnessRadix.AllocatedAwayBelow
import InitECandidate.Solver.WitnessRadix.AllocatedAway

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString

/-- Hashing into its actual fresh output retains every older live object;
the scratch buffers are below the persistent allocation region. -/
theorem hash {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (populations : ∀ index,(objects index).slots.length ≤ population) (environment : WarmKeys.Environment source)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (hashEnvironment : Keccak256.Environment source stp scratch) (buffers : Keccak256.Buffers stp pointer scratch out length)
    (aligned : out.toNat % 8 = 0) (stateBelow : stp.toNat + 200 ≤ cutoff) (scratchBelow : scratch.toNat + 136 ≤ cutoff)
    (protectedBelow : protectedCursor ≤ out.toNat) (outputBefore : out.toNat ≤ cursor)
    (floors : ∀ index,cutoff ≤ (objects index).floor)
    (poolsBefore : ∀ index pool,(objects index).plan.base pool + size (objects index).kind (objects index).plan pool ≤ out.toNat)
    (registry : AccountDecode.Registry source cutoff out.toNat objects accounts)
    (journalAbove : cutoff ≤ base) (journalBefore : base + 32 * cap ≤ out.toNat)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (Keccak256.values pointer out length))
    (code : source.code.lookup (ofString "keccak256") = some (Keccak256.formals,Keccak256.body,.one))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments) = (none,post)) :
    post.locals = source.locals ∧
      Result source post cursor cursor cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property (Keccak256.price length + 1) 0 population := by
  obtain ⟨locals,forward,clock,control,memory⟩ := Keccak256.call_normal source post arguments stp pointer scratch out length args code
    (Keccak256.allocated_entry source stp pointer scratch out length hashEnvironment buffers) (by have := buffers.inputArena.upper; omega) normal
  have codes : post.code = source.code := congrArg (fun s => s.code) control
  have domain : post.memaddrs = source.memaddrs := congrArg (fun s => s.memaddrs) control
  have endian : post.be = source.be := congrArg (fun s => s.be) control
  have globals : post.globals = source.globals := congrArg (fun s => s.globals) control
  have oracle : post.ffi.oracle = source.ffi.oracle := congrArg (fun s => s.ffi.oracle) control
  have unchanged (query : BitVec 64) (above : cutoff ≤ query.toNat) (earlier : query.toNat < out.toNat) : post.memory query = source.memory query :=
    memory query ⟨AllocatedBytes.Arena.away_above stp query 200 buffers.stateArena (by omega),
      AllocatedBytes.Arena.away_above scratch query 136 buffers.scratchArena (by omega),
      AllocatedBytes.Arena.away_below out query 32 buffers.outputArena aligned earlier⟩
  have pools : ∀ index,MemoryModel.PoolFrame source.memory post.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply unchanged
    · rw [number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
      have floor := floors index
      have lower := (family.tables index).lower pool
      omega
    · rw [number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
      have before := poolsBefore index pool
      omega
  have nextFamily := family.of_pools (congrArg (fun g => g.lookup (ofString "heap_ptr")) globals) domain endian pools
  have frame : TableFamily.PersistentFrame cutoff out.toNat objects objects source post :=
    ⟨fun query above earlier outside => ⟨outside,unchanged query above earlier⟩⟩
  have nextRegistry := registry.framed source post cutoff out.toNat cursor objects objects accounts frame outputBefore domain
  have nextImage : Journal.Image post objects base count entries := image.transfer domain (fun _ => rfl) (fun _ => rfl)
    (by
      intro index inside field
      have n := Journal.entry_number base cap index field zone.valid (by omega)
      have f := field.isLt
      apply unchanged
      · rw [n]; omega
      · rw [n]; omega) image.separate
  refine ⟨locals,{
    clockForward := forward
    cursorForward := Nat.le_refl _
    protectedBefore := Nat.le_trans protectedBelow outputBefore
    countForward := Nat.le_refl _
    countBound := countBound
    appends := by omega
    family := nextFamily
    image := nextImage
    zone := zone
    work := by omega
    populations := populations
    code := codes
    oracle := oracle
    environment := environment.of_fields codes domain endian
    globals := fun key _ _ => congrArg (fun g => g.lookup key) globals
    values := values.of_pools source post objects cursor family property pools
    savedValues := savedValues
    registry := nextRegistry
    extension := AccountDecode.Registry.Extension.refl accounts cursor
    effect := by simpa only [Nat.sub_self] using Journal.CounterEffect.unchanged source post (congrArg (fun g => g.lookup (ofString "journal_n")) globals)
    metadata := TableFamily.Metadata.refl objects
    frame := fun query above earlier outside _ => ⟨outside,unchanged query above (Nat.lt_of_lt_of_le earlier protectedBelow)⟩
    counter := (congrArg (fun g => g.lookup (ofString "journal_n")) globals).trans counter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known => known }⟩

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.hash
