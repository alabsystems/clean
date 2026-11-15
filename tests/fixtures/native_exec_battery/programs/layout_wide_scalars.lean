structure Wide where
  f0 : UInt64
  f1 : UInt64
  f2 : UInt64
  f3 : UInt64
  f4 : UInt64
  f5 : UInt64
  f6 : UInt64
  f7 : UInt64
  f8 : UInt64
  f9 : UInt64
  f10 : UInt64
  f11 : UInt64
  f12 : UInt64
  f13 : UInt64
  f14 : UInt64
  f15 : UInt64
  f16 : UInt64
  f17 : UInt64
  f18 : UInt64
  f19 : UInt64
  f20 : UInt64
  f21 : UInt64
  f22 : UInt64
  f23 : UInt64
  f24 : UInt64
  f25 : UInt64
  f26 : UInt64
  f27 : UInt64
  f28 : UInt64
  f29 : UInt64
  f30 : UInt64
  f31 : UInt64
  f32 : UInt64
  f33 : UInt64
  f34 : UInt64
  f35 : UInt64
  f36 : UInt64
  f37 : UInt64
  f38 : UInt64
  f39 : UInt64

def Wide.mk' (n : UInt64) : Wide := { f0 := n, f1 := n, f2 := n, f3 := n, f4 := n, f5 := n, f6 := n, f7 := n, f8 := n, f9 := n, f10 := n, f11 := n, f12 := n, f13 := n, f14 := n, f15 := n, f16 := n, f17 := n, f18 := n, f19 := n, f20 := n, f21 := n, f22 := n, f23 := n, f24 := n, f25 := n, f26 := n, f27 := n, f28 := n, f29 := n, f30 := n, f31 := n, f32 := n, f33 := n, f34 := n, f35 := n, f36 := n, f37 := n, f38 := n, f39 := n }

def main : IO Unit := IO.println (toString (Wide.mk' 41).f39)
