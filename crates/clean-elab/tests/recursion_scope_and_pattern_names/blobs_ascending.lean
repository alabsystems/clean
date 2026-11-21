namespace SemR
def bytesLt : List Nat → List Nat → Bool
  | a :: as, b :: bs => if a == b then bytesLt as bs else decide (a < b)
  | _, _ => false

def blobsAscending : List (List Nat × List Nat) → Bool
  | a :: b :: rest => bytesLt a.1 b.1 && blobsAscending (b :: rest)
  | _ => true
end SemR
namespace SemR
theorem ascending_empty : blobsAscending [] = true := rfl
theorem ascending_one (a : List Nat × List Nat) : blobsAscending [a] = true := rfl
theorem ascending_step (a b : List Nat × List Nat) (xs : List (List Nat × List Nat)) :
    blobsAscending (a :: b :: xs) = (bytesLt a.1 b.1 && blobsAscending (b :: xs)) := rfl
theorem ascending_later_duplicate :
    blobsAscending [([1],[]),([2],[7]),([2],[9])] = false := rfl
theorem ascending_increasing : blobsAscending [([1],[]),([2],[7]),([3],[9])] = true := rfl
end SemR
