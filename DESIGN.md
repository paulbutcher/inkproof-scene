# Inkproof.Scene design

## Raster model

The model (`Inkproof/Scene/Raster.lean`) is the specification that renderers must match. Coordinates are exact rationals, so no statement involves floating point. A primitive is a set of points (`Region`); pixel `(col, row)` is the closed square `[col, col + 1] × [row, row + 1]`; a primitive covers a pixel when it meets the square. Boundaries count, so touching an edge or corner covers the pixel. A centre-sampling rule is rejected because it can drop a thin feature such as a one-sample spike, which would break the guarantees that aggregation preserves the picture.

Anti-aliasing is not in the model. Shaders may shade partial coverage, which is a documented, deliberate difference; it does not remove pixels the model covers, but it can fade them.

## Display list

A display list is an array of commands, each with a layer, a colour and a shape: line strip, min/max envelope, filled area, rectangle, marker or text. Strips, envelopes and areas are lists of values and explicit gaps; nothing is drawn across a gap. Commands paint in ascending layer, then list order. A thick strip is its polyline thickened by a Euclidean half-width (round joins and caps). Text is modelled by its layout box, since glyph shapes belong to the renderer.

## Clipping

`DisplayList.clip` restricts every command to a rectangle (`Shape.clip`): rectangles and square markers are cut exactly, and every other shape is wrapped in `Shape.clipped`, a scissor whose region is the shape's intersection with the rectangle. A command with nothing inside the rectangle is dropped. `Shape.clip_region` proves that the clipped region is exactly the original's points inside the rectangle, and `DisplayList.clip_covers_of_inside` that no pixel wholly inside the rectangle loses coverage.

## Line triangles

`stripTriangles` turns a strip of positive half-width into triangles, two per segment and per lone value. Each segment's rectangle is extended by the half-width at both ends (square caps, which contain the model's round caps) and is measured against a rational lower bound of the segment's length instead of the exact length, so the generated geometry is a little wider than the model's, never narrower. There is no join geometry: adjacent rectangles overlap, which contains the model's round joins. `strip_covers_triangles` proves that every pixel the model says a strip covers is covered by one of its triangles. A zero half-width strip has no area and is left to the renderer as a hairline.

Anti-aliased geometry, where a renderer chooses it, fades the outer edge of these triangles. It differs from the aliased model by shading partial coverage, so it can lower the opacity of a pixel the model covers but never leaves a covered pixel unreached by geometry; guarantees stated under the model (TCB-2) hold for the geometry, not for the shaded values.

## Chart compilation

A `Projection` takes data coordinates to grid coordinates (`Projection.linear` from two linear scales). Series are `Segmented`, and a missing value is a gap like a break, so `Projection.runs` yields runs of consecutive present points of one segment; every strip and area is the runs separated by explicit gaps (`compileLine_no_bridge`, `compileArea_no_bridge`).

With `reduce`, each run is cut into maximal stretches of adjacent points in one x class (`xKey`: an integer, or the open interval between two) and each stretch becomes its first point, its lowest and highest values at the first point's x, and its last point (`reduceRun`, built on Core's first/last/minimum/maximum aggregates). `compileLine_covers_iff` proves a bare line (half-width zero) covers the same pixels as the full data. It needs no assumption on the data: a stretch is replaced only where every column touched is the same for all its points, and the segments between stretches are kept. Sorted data merely makes each class one stretch. A thick line is not covered: moving the extremes to the first point's x can shift it by under a pixel.

The compilers work on lists and are meant for a tile or a viewport's worth of points.

## Reference rasterizer

`Shape.meetsB` decides, in exact rational arithmetic, whether a shape's region meets a closed window, and `Shape.meetsB_iff` proves it agrees with `Shape.region`, so the rasterizer's coverage is the model's for every command kind. Each primitive reduces to a few exact tests (`Meet.lean`): a segment against a window is a feasibility problem in the segment parameter; a thickened segment against a window is the window widened sideways, widened vertically, and four corner discs; a swept quadrilateral is four such problems, one per ordering of its ends; a clipped shape is tested against the window intersected with the scissor. The test is per pixel and per command with no bounding-box culling, which keeps the proof direct and makes it a reference rather than a fast renderer.

`render` gives each pixel the colour of the command on top there (`winner`: the covering command of greatest layer, the last in the list among those) or the background when none covers it; `pixelColor_of_covers` and `pixelColor_of_not_covers` state this. Painting replaces the colour outright: blending is not part of the model.

