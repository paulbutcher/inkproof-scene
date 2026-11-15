/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene
import InkproofTools.Test.Platform

open InkproofTools.Test

def main (args : List String) : IO UInt32 :=
  runTests [platformTest (args.contains "--expect-wasm")]
