namespace SemR
def shaWords : List Nat → List Nat
  | a :: b :: c :: d :: rest => (a * 16777216 + b * 65536 + c * 256 + d) :: shaWords rest
  | _ => []
end SemR
theorem law_nil : SemR.shaWords [] = [] := rfl
theorem law_one (a : Nat) : SemR.shaWords [a] = [] := rfl
theorem law_two (a b : Nat) : SemR.shaWords [a,b] = [] := rfl
theorem law_three (a b c : Nat) : SemR.shaWords [a,b,c] = [] := rfl
theorem law_chunk (a b c d : Nat) (xs : List Nat) : SemR.shaWords (a::b::c::d::xs) = (a * 16777216 + b * 65536 + c * 256 + d) :: SemR.shaWords xs := rfl

namespace Scratch
def chunks : List Nat → List Nat × List Nat × List Nat × List Nat
  | [] => ([], [], [], [])
  | a :: xs =>
    let previous := chunks xs
    let result := match xs with
      | b :: c :: d :: _ => (a * 16777216 + b * 65536 + c * 256 + d) :: previous.2.2.2
      | _ => []
    (result, previous.1, previous.2.1, previous.2.2.1)
def result (xs : List Nat) : List Nat := (chunks xs).1
end Scratch

theorem actual_compiler_window (xs : List Nat) : SemR.shaWords xs = Scratch.result xs := rfl
