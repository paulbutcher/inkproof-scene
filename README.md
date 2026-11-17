# Inkproof.Scene

The display list for Inkproof charts, the compilers that produce it, and a reference rasterizer that defines what it means. Part of Inkproof. Released under the Apache 2.0 license; see `LICENSE`.

## What it does

- Describe a drawing as a display list of layered, coloured shapes (rectangles, line strips, areas, envelopes, markers, text, clipped groups): `DisplayList`, `Command`, `Shape`, `Paint`, `Color`.
- Compile chart data into display-list commands through a projection from data to plane coordinates: `Projection`, `compileLine`, `compileArea`, `compileBars`, `compileScatter`, `compileHeatmap`, `compileEnvelope`.
- Draw a line, area or envelope with gaps where data is missing, so no stroke bridges an absent value: `Item`, `runsOf`, `Item.ofRuns`, `compileEnvelope`.
- Thin dense line data without changing its look: `reducePoints`, `reduceRun`, `groupByKey`.
- Clip a display list to a rectangle: `DisplayList.clip`, `Command.clip`, `Shape.clip`, `Rect.meet`.
- Find which commands paint a pixel, and in what order: `DisplayList.paintOrder`, `DisplayList.Covers`, `Command.Covers`, `winner`.
- State exactly which pixels a shape covers (the raster model a GPU renderer must match): `Shape.region`, `Region`, `Region.Covers`, `Pixel`, `Window`, `Grid`.
- Rasterize a display list to an image, the reference for any other renderer: `render`, `pixelColor`, `Image`.
- Pick colours, dash styles and markers for series in light and dark themes with checked contrast: `Theme`, `Theme.series`, `Theme.seriesStyle`, `Color.contrast`.

## Requiring it

```lean
require «inkproof-scene» from git "https://github.com/paulbutcher/inkproof-scene" @ "v0.8.0"
```
