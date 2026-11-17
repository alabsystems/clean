module
import all StableFixture.Defs
theorem logical : StableFixture.addOffset (StableFixture.twice 20) = 41 := rfl
#eval StableFixture.addOffset (StableFixture.twice 20)
