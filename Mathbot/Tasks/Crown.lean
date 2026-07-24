/-!
Small CROWN-style upper-bound carrier theorem.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Crown

inductive UpperBoundReplay : Int → Int → Prop where
  | refl (value : Int) :
      UpperBoundReplay value value
  | add {x xUpper y yUpper : Int} :
      UpperBoundReplay x xUpper →
      UpperBoundReplay y yUpper →
      UpperBoundReplay (x + y) (xUpper + yUpper)
  | outputEq {value upper output : Int} :
      output = upper →
      UpperBoundReplay value upper →
      UpperBoundReplay value output

structure TwoInputUpperBound where
  xUpper : Int
  yUpper : Int
  bias : Int
  output : Int

def validTwoInputUpperBound (cert : TwoInputUpperBound) : Prop :=
  cert.output = cert.xUpper + cert.yUpper + cert.bias

theorem crown_two_input_upper_sound
    (x y : Int)
    (cert : TwoInputUpperBound)
    (hx : UpperBoundReplay x cert.xUpper)
    (hy : UpperBoundReplay y cert.yUpper)
    (hcert : validTwoInputUpperBound cert) :
    UpperBoundReplay (x + y + cert.bias) cert.output := by
  unfold validTwoInputUpperBound at hcert
  exact
    UpperBoundReplay.outputEq hcert
      (UpperBoundReplay.add (UpperBoundReplay.add hx hy) (UpperBoundReplay.refl cert.bias))

end Mathbot.Tasks.Crown
