/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InkproofTools.AxiomCheck
import Inkproof.Scene

open Lean Elab Command

run_cmd liftCoreM (InkproofTools.AxiomCheck.check `Inkproof.Scene none)
