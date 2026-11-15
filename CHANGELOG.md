# Changelog

## v0.3.0

- A pure-Lean reference rasterizer from a display list to a pixel buffer, proved to paint exactly the pixels the raster model covers, in layer order.

## v0.2.0

- Clipping of display lists to a rectangle, with a proof against the raster model.
- Triangle geometry for thick lines, with a proof against the raster model.

## v0.1.0

- The display list and the aliased, touch-based raster model, with proofs that a primitive covers every pixel it touches and that coverage is monotone under union.
