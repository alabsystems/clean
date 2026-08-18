import Lake
open Lake DSL

package demo

lean_lib Demo

/-- A custom target the declarative subset does not model. -/
target generateAssets pkg : System.FilePath := do
  let out := pkg.buildDir / "assets"
  pure out
