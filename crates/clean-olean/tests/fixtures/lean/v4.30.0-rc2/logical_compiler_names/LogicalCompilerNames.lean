-- Ordinary logical declarations that collide with historical compiler hints.
module
prelude
public import Init.Prelude

public structure Ordinary where
  protected _specFinalizedAt : Type
  protected _lambdaField : Type

public def Ordinary.use (s : Ordinary) : Type := s._specFinalizedAt
public def Logical._spec (x : Type) : Type := x
public def Logical._lambda_1 (x : Type) : Type := x
public def Logical._rarg (x : Type) : Type := x
public def Logical._unsafe_rec (x : Type) : Type := x
public def Logical._specification (x : Type) : Type := x
public def Logical._spec_1.nested (x : Type) : Type := x
public def Logical._elambda_1.nested (x : Type) : Type := x
public def Logical.«Quoted._spec_1» (x : Type) : Type := x
