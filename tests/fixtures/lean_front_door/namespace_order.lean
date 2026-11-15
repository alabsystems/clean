-- A block's messages come out in source order.
namespace A
#eval 1
theorem s : 2 = 2 := sorry
#eval 3
end A
