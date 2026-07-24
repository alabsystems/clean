/-!
Tiny exact Farkas-style certificate replay.

This is deliberately small: it models the certificate shape needed by a neural
verification exporter without importing Mathlib or trusting an arithmetic
oracle.
-/

set_option autoImplicit false

namespace Mathbot.Tasks.Farkas

inductive UpperBoundReplay : Int → Int → Prop where
  | add {x xUpper y yUpper : Int} :
      UpperBoundReplay x xUpper →
      UpperBoundReplay y yUpper →
      UpperBoundReplay (x + y) (xUpper + yUpper)
  | outputEq {value upper output : Int} :
      output = upper →
      UpperBoundReplay value upper →
      UpperBoundReplay value output

structure TwoRowUpperCertificate where
  useX : Bool
  useY : Bool
  output : Int

def validTinyUpperCertificate (cert : TwoRowUpperCertificate) : Prop :=
  cert.useX = true ∧ cert.useY = true ∧ cert.output = 5

theorem gamma_farkas_two_row_upper_sound
    (x y : Int)
    (hx : UpperBoundReplay x 2)
    (hy : UpperBoundReplay y 3)
    (cert : TwoRowUpperCertificate)
    (hcert : validTinyUpperCertificate cert) :
    UpperBoundReplay (x + y) cert.output := by
  unfold validTinyUpperCertificate at hcert
  exact UpperBoundReplay.outputEq hcert.2.2 (UpperBoundReplay.add hx hy)

end Mathbot.Tasks.Farkas
