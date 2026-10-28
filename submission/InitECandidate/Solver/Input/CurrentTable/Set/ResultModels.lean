import InitECandidate.Solver.Input.CurrentTable.Set.Result
import InitECandidate.Solver.Input.CurrentTable.Set.UpdateImage
import InitECandidate.Solver.Input.CurrentTable.Set.InsertedImage
import InitECandidate.Solver.Input.CurrentTable.Set.InsertedBefore

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem update_result {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root value leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (marked : bits leaf = 256) (validValue : ValueOf value) :
    Result source (updated source table cap leaf value) table cap count ValueOf :=
  ⟨⟨root,next,count,valid,bits,left,right,keys,update_image image member marked validValue,by omega⟩,
    node_metadata source (New.nodesPointer table cap) leaf value 8,update_before image member⟩

theorem inserted_result {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    Result source (insertedState source table cap node parent pointer value next count difference query left) table cap count ValueOf :=
  ⟨⟨_,_,_,_,_,_,_,_,inserted_image data,by omega⟩,
    inserted_metadata source table cap node parent pointer value next count difference query left,inserted_before data⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_result
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_result
