/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scene.Shading

namespace Inkproof.Scene

/-- How text is set: a CSS font family, a size in pixels and a colour. The host's text layer applies it to the labels and titles it is given. -/
structure TextStyle where
  family : String := "sans-serif"
  size : Rat := 10
  color : Color := Color.black

/-- The default style of an axis title, a little larger than a tick label. -/
def TextStyle.axisTitle : TextStyle := { size := 12 }

theorem TextStyle.default_size : ({} : TextStyle).size = 10 := rfl

theorem TextStyle.axisTitle_size : TextStyle.axisTitle.size = 12 := rfl

end Inkproof.Scene
