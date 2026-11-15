# Inkproof.Scene design

## Raster model

The model (`Inkproof/Scene/Raster.lean`) is the specification that renderers must match. Coordinates are exact rationals, so no statement involves floating point. A primitive is a set of points (`Region`); pixel `(col, row)` is the closed square `[col, col + 1] × [row, row + 1]`; a primitive covers a pixel when it meets the square. Boundaries count, so touching an edge or corner covers the pixel. A centre-sampling rule is rejected because it can drop a thin feature such as a one-sample spike, which would break the guarantees that aggregation preserves the picture.

Anti-aliasing is not in the model. Shaders may shade partial coverage, which is a documented, deliberate difference; it does not remove pixels the model covers, but it can fade them.

## Display list

A display list is an array of commands, each with a layer, a colour and a shape: line strip, min/max envelope, filled area, rectangle, marker or text. Strips, envelopes and areas are lists of values and explicit gaps; nothing is drawn across a gap. Commands paint in ascending layer, then list order. A thick strip is its polyline thickened by a Euclidean half-width (round joins and caps). Text is modelled by its layout box, since glyph shapes belong to the renderer.
