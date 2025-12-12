//
// MeshSynth.swift
// Procedural City / Road Network Generator
// - generates road graph using Poisson-disc / spanning + relaxation
// - creates blocks, places buildings with heights
// - exports GeoJSON and prints an ASCII map preview
//
// Swift 5+
//

import Foundation
import CoreGraphics

// ---------------------------
// Utilities
// ---------------------------
struct Rng {
    private var state: UInt64
    init(seed: UInt64) { state = seed == 0 ? 0xdeadbeefcafebabe : seed }
    mutating func next() -> UInt64 {
        state &+= 0x9e3779b97f4a7c15
        var z = state
        z = (z ^ (z >> 30)) &* 0xbf58476d1ce4e5b9
        z = (z ^ (z >> 27)) &* 0x94d049bb133111eb
        return z ^ (z >> 31)
    }
    mutating func nextDouble(_ lo: Double = 0, _ hi: Double = 1) -> Double {
        let v = next()
        let x = Double(v & 0xFFFFFFFF) / Double(0x1_0000_0000)
        return lo + (hi - lo) * x
    }
}

typealias Point = (x: Double, y: Double)

func distance(_ a: Point, _ b: Point) -> Double {
    let dx = a.x - b.x; let dy = a.y - b.y
    return sqrt(dx*dx + dy*dy)
}

// ---------------------------
// Poisson Disk Sampling (2D) - Bridson's algorithm
// ---------------------------
func poissonDisk(width: Double, height: Double, r: Double, k: Int = 30, seed: UInt64 = 12345) -> [Point] {
    var rng = Rng(seed: seed)
    let cellSize = r / sqrt(2)
    let cols = Int(ceil(width / cellSize))
    let rows = Int(ceil(height / cellSize))
    var grid = Array(repeating: Array(repeating: Point?(nil), count: cols), count: rows)
    func gridCoords(_ p: Point) -> (Int,Int) {
        return (min(rows-1, max(0, Int(p.y / cellSize))), min(cols-1, max(0, Int(p.x / cellSize))))
    }
    var samplePoints: [Point] = []
    var process: [Point] = []
    let initial = (rng.nextDouble(0, width), rng.nextDouble(0, height))
    samplePoints.append(initial); process.append(initial)
    let (ir, ic) = gridCoords(initial); grid[ir][ic] = initial
    while !process.isEmpty {
        let idx = Int(rng.nextDouble(0, Double(process.count)))
        let p = process[idx]
        var found = false
        for _ in 0..<k {
            let a = rng.nextDouble(0, 2*Double.pi)
            let rr = r * (1 + rng.nextDouble(0,1))
            let nx = p.x + cos(a) * rr
            let ny = p.y + sin(a) * rr
            if nx < 0 || nx >= width || ny < 0 || ny >= height { continue }
            let np = (nx, ny)
            let (gr, gc) = gridCoords(np)
            var ok = true
            let minR = max(0, gr-2), maxR = min(rows-1, gr+2)
            let minC = max(0, gc-2), maxC = min(cols-1, gc+2)
            for rr2 in minR...maxR {
                for cc2 in minC...maxC {
                    if let q = grid[rr2][cc2] {
                        if distance(q, np) < r { ok = false; break }
                    }
                }
                if !ok { break }
            }
            if ok {
                samplePoints.append(np)
                process.append(np)
                grid[gr][gc] = np
                found = true
            }
        }
        if !found {
            process.remove(at: idx)
        }
    }
    return samplePoints
}

// ---------------------------
// Road Graph: connect points via Delaunay-like spanning (greedy MST + k-nearest)
// ---------------------------
struct RoadNode {
    let id: Int
    let p: Point
}
struct RoadEdge {
    let a: Int
    let b: Int
    let length: Double
}

func buildRoadGraph(points: [Point], kNeighbors: Int = 6) -> ([RoadNode], [RoadEdge]) {
    var nodes = points.enumerated().map { RoadNode(id: $0.offset, p: $0.element) }
    var edges: [RoadEdge] = []
    // knn edges
    for i in 0..<nodes.count {
        let distances = nodes.enumerated().filter { $0.offset != i }.map { ($0.offset, distance(nodes[i].p, $0.element.p)) }
        let knn = distances.sorted { $0.1 < $1.1 }.prefix(kNeighbors)
        for (j, d) in knn {
            edges.append(RoadEdge(a: i, b: j, length: d))
        }
    }
    // add MST to ensure connectivity (Kruskal)
    var parent = Array(0..<nodes.count)
    func find(_ x: Int) -> Int { parent[x] == x ? x : { parent[x] = find(parent[x]); return parent[x] }() }
    func unify(_ a: Int, _ b: Int) {
        let ra = find(a), rb = find(b); if ra != rb { parent[rb] = ra }
    }
    let allEdges = edges.sorted { $0.length < $1.length }
    var used: [RoadEdge] = []
    for e in allEdges {
        if find(e.a) != find(e.b) { used.append(e); unify(e.a, e.b) }
    }
    // combine MST + short knn edges as final graph (avoid duplicates)
    var finalEdges = used
    for e in edges {
        if !finalEdges.contains(where: { ($0.a == e.a && $0.b == e.b) || ($0.a == e.b && $0.b == e.a) }) {
            // apply length threshold
            if e.length < 200 { finalEdges.append(e) }
        }
    }
    // normalize and unique
    finalEdges = finalEdges.map { $0.a < $0.b ? $0 : RoadEdge(a: $0.b, b: $0.a, length: $0.length) }
    var uniq: [RoadEdge] = []
    for e in finalEdges {
        if !uniq.contains(where: { $0.a == e.a && $0.b == e.b }) { uniq.append(e) }
    }
    return (nodes, uniq)
}

// ---------------------------
// Polygonize blocks from planar graph (very simple face extraction)
// We'll rasterize graph edges into grid and floodfill to extract cells (blocks)
// ---------------------------
func rasterizeBlocks(nodes: [RoadNode], edges: [RoadEdge], width: Int, height: Int, worldW: Double, worldH: Double) -> [[(Int,Int)]] {
    // grid
    var grid = Array(repeating: Array(repeating: 0 as Int, count: width), count: height)
    func worldToGrid(_ p: Point) -> (Int,Int) {
        let gx = Int((p.x / worldW) * Double(width-1))
        let gy = Int((p.y / worldH) * Double(height-1))
        return (gx, gy)
    }
    // mark edges
    for e in edges {
        let a = nodes[e.a].p, b = nodes[e.b].p
        let (ax, ay) = worldToGrid(a), (bx, by) = worldToGrid(b)
        // Bresenham line
        var x0 = ax, y0 = ay, x1 = bx, y1 = by
        let dx = abs(x1 - x0), sx = x0 < x1 ? 1 : -1
        let dy = -abs(y1 - y0), sy = y0 < y1 ? 1 : -1
        var err = dx + dy
        while true {
            if x0 >= 0 && x0 < width && y0 >= 0 && y0 < height { grid[y0][x0] = 1 }
            if x0 == x1 && y0 == y1 { break }
            let e2 = 2 * err
            if e2 >= dy { err += dy; x0 += sx }
            if e2 <= dx { err += dx; y0 += sy }
        }
    }
    // flood fill empty regions as blocks
    var visited = Array(repeating: Array(repeating: false, count: width), count: height)
    var blocks: [[(Int,Int)]] = []
    for y in 0..<height {
        for x in 0..<width {
            if grid[y][x] == 0 && !visited[y][x] {
                // BFS
                var q: [(Int,Int)] = [(x,y)]; visited[y][x] = true; var comp: [(Int,Int)] = []
                while !q.isEmpty {
                    let (cx, cy) = q.removeFirst()
                    comp.append((cx,cy))
                    for (nx, ny) in [(cx+1,cy),(cx-1,cy),(cx,cy+1),(cx,cy-1)] {
                        if nx >= 0 && nx < width && ny >= 0 && ny < height && !visited[ny][nx] && grid[ny][nx] == 0 {
                            visited[ny][nx] = true; q.append((nx,ny))
                        }
                    }
                }
                if comp.count > 10 { blocks.append(comp) }
            }
        }
    }
    return blocks
}

// ---------------------------
// Building placement: within each block, place a grid of small buildings with variable heights
// ---------------------------
struct Building {
    let footprint: [(Double,Double)]
    let height: Double
}

func placeBuildingsInBlock(cells: [(Int,Int)], gridW: Int, gridH: Int, worldW: Double, worldH: Double, seed: UInt64) -> [Building] {
    var rng = Rng(seed: seed ^ UInt64(cells.count))
    // compute bounding box in world units
    let xs = cells.map { Double($0.0) / Double(gridW) * worldW }
    let ys = cells.map { Double($0.1) / Double(gridH) * worldH }
    guard let minx = xs.min(), let maxx = xs.max(), let miny = ys.min(), let maxy = ys.max() else { return [] }
    let bw = max(1.0, (maxx - minx) / 6.0), bh = max(1.0, (maxy - miny) / 6.0)
    var buildings: [Building] = []
    for gx in 0..<6 {
        for gy in 0..<6 {
            let x0 = minx + Double(gx) * bw + rng.nextDouble(0, bw*0.2)
            let y0 = miny + Double(gy) * bh + rng.nextDouble(0, bh*0.2)
            let x1 = x0 + bw * (0.7 + rng.nextDouble(0,0.6))
            let y1 = y0 + bh * (0.7 + rng.nextDouble(0,0.6))
            if x1 - x0 < 0.2 || y1 - y0 < 0.2 { continue }
            let h = 5.0 + rng.nextDouble(0, 60)
            let footprint = [(x0,y0),(x1,y0),(x1,y1),(x0,y1)]
            buildings.append(Building(footprint: footprint, height: h))
        }
    }
    return buildings
}

// ---------------------------
// GeoJSON export
// ---------------------------
func geoJSONFeatures(nodes: [RoadNode], edges: [RoadEdge], blocks: [[(Int,Int)]], buildings: [[Building]], worldW: Double, worldH: Double, gridW: Int, gridH: Int) -> [String:Any] {
    var features: [[String:Any]] = []
    // edges as LineStrings
    for e in edges {
        let a = nodes[e.a].p; let b = nodes[e.b].p
        let geom: [String:Any] = ["type":"LineString", "coordinates":[ [a.x, a.y], [b.x, b.y] ]]
        let props = ["type":"road","length": e.length]
        features.append(["type":"Feature", "geometry":geom, "properties":props])
    }
    // blocks as polygons (approx from cell centers)
    for (i, block) in blocks.enumerated() {
        // convert cell list to polygon by convex hull of their centers
        let centers = block.map { (Double($0.0)/Double(gridW)*worldW, Double($0.1)/Double(gridH)*worldH) }
        let hull = convexHull(points: centers)
        let coords = hull.map { [$0.0, $0.1] } + [ [hull[0].0, hull[0].1] ]
        let geom: [String:Any] = ["type":"Polygon", "coordinates":[coords]]
        let props = ["type":"block","cells": block.count]
        features.append(["type":"Feature", "geometry":geom, "properties":props])
        // buildings
        if i < buildings.count {
            for b in buildings[i] {
                let coordsB = b.footprint.map { [$0.0, $0.1] } + [ [b.footprint[0].0, b.footprint[0].1] ]
                let geomB: [String:Any] = ["type":"Polygon", "coordinates":[coordsB]]
                let propsB: [String:Any] = ["type":"building","height":b.height]
                features.append(["type":"Feature", "geometry":geomB, "properties":propsB])
            }
        }
    }
    return ["type":"FeatureCollection", "features": features]
}

// Simple convex hull (Monotone chain) for 2D points
func convexHull(points: [(Double,Double)]) -> [(Double,Double)] {
    let pts = points.sorted { $0.0 == $1.0 ? $0.1 < $1.1 : $0.0 < $1.0 }
    if pts.count <= 2 { return pts }
    func cross(_ o:(Double,Double), _ a:(Double,Double), _ b:(Double,Double)) -> Double {
        (a.0 - o.0) * (b.1 - o.1) - (a.1 - o.1) * (b.0 - o.0)
    }
    var lower: [(Double,Double)] = []
    for p in pts {
        while lower.count >= 2 && cross(lower[lower.count-2], lower[lower.count-1], p) <= 0 { lower.removeLast() }
        lower.append(p)
    }
    var upper: [(Double,Double)] = []
    for p in pts.reversed() {
        while upper.count >= 2 && cross(upper[upper.count-2], upper[upper.count-1], p) <= 0 { upper.removeLast() }
        upper.append(p)
    }
    lower.removeLast(); upper.removeLast()
    return lower + upper
}

// ---------------------------
// ASCII renderer
// ---------------------------
func asciiPreview(nodes: [RoadNode], edges: [RoadEdge], blocks: [[(Int,Int)]], gridW: Int, gridH: Int) -> String {
    var canvas = Array(repeating: Array(repeating: " ", count: gridW), count: gridH)
    // mark roads
    for e in edges {
        let a = nodes[e.a].p, b = nodes[e.b].p
        let (ax, ay) = (Int(a.x/1.0), Int(a.y/1.0)) // we assume world coords mapped already
        let (bx, by) = (Int(b.x/1.0), Int(b.y/1.0))
        // interpolate in grid
        let len = max(1, Int(e.length / 8.0))
        for t in 0...len {
            let fx = Double(t)/Double(len) * (b.x - a.x) + a.x
            let fy = Double(t)/Double(len) * (b.y - a.y) + a.y
            let gx = max(0, min(gridW-1, Int(fx / Double(gridW) * Double(gridW))))
            let gy = max(0, min(gridH-1, Int(fy / Double(gridH) * Double(gridH))))
            canvas[gy][gx] = "#"
        }
    }
    // mark blocks
    for b in blocks {
        for (x,y) in b {
            let gx = max(0, min(gridW-1, x))
            let gy = max(0, min(gridH-1, y))
            if canvas[gy][gx] == " " { canvas[gy][gx] = "." }
        }
    }
    // build string
    var s = ""
    for row in canvas {
        s += row.joined() + "\n"
    }
    return s
}

// ---------------------------
// Main driver
// ---------------------------
func runMeshSynth(seed: UInt64 = 2025, worldW: Double = 2000, worldH: Double = 1200) {
    print("MeshSynth — procedural city generator (seed \(seed))")
    // 1) sample Poisson points for road nodes
    let spacing = 120.0
    let pts = poissonDisk(width: worldW, height: worldH, r: spacing, k: 32, seed: seed)
    print("Sampled \(pts.count) nodes")
    // 2) build road graph
    let (nodes, edges) = buildRoadGraph(points: pts, kNeighbors: 6)
    print("Built road graph: nodes \(nodes.count), edges \(edges.count)")
    // 3) rasterize blocks
    let gridW = 120, gridH = 72
    let blocks = rasterizeBlocks(nodes: nodes, edges: edges, width: gridW, height: gridH, worldW: worldW, worldH: worldH)
    print("Extracted \(blocks.count) blocks")
    // 4) place buildings inside blocks
    var allBuildings: [[Building]] = []
    for (i, b) in blocks.enumerated() {
        let bs = placeBuildingsInBlock(cells: b, gridW: gridW, gridH: gridH, worldW: worldW, worldH: worldH, seed: seed ^ UInt64(i*7919))
        allBuildings.append(bs)
    }
    // 5) export geojson
    let gj = geoJSONFeatures(nodes: nodes, edges: edges, blocks: blocks, buildings: allBuildings, worldW: worldW, worldH: worldH, gridW: gridW, gridH: gridH)
    let jsonData = try! JSONSerialization.data(withJSONObject: gj, options: [.prettyPrinted, .sortedKeys])
    let outURL = FileManager.default.homeDirectoryForCurrentUser.appendingPathComponent("meshsynth_city.geojson")
    try? jsonData.write(to: outURL)
    print("Exported GeoJSON to \(outURL.path)")
    // 6) ascii preview
    let preview = asciiPreview(nodes: nodes, edges: edges, blocks: blocks, gridW: 100, gridH: 40)
    print("\nASCII Preview:\n")
    print(preview)
}

// Run with default seed
runMeshSynth(seed: 2025)
