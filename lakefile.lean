/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-scene» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-float» from git "https://github.com/paulbutcher/inkproof-float" @ "v0.5.0"
require «inkproof-core» from git "https://github.com/paulbutcher/inkproof-core" @ "v0.8.0"
require «inkproof-scale» from git "https://github.com/paulbutcher/inkproof-scale" @ "v0.6.1"
require «inkproof-axis» from git "https://github.com/paulbutcher/inkproof-axis" @ "v0.5.4"

@[default_target]
lean_lib InkproofScene where
  roots := #[`Inkproof.Scene]

@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
