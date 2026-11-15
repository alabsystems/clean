mutual
inductive BadHighA : Type where
  | mk : Type → BadHighB → BadHighA
inductive BadHighB : Type where
  | mk : BadHighA → BadHighB
end
