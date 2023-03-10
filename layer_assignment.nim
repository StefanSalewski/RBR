# The layer assignment algorithm for our topological printed circuit board router
# follows very closely the detailed description in Tal Dayan's PhD thesis.
#
# Currently we do not divide the PCB board into multiple 'Bins', but identify the whole
# board with one large bin, which is routed by our router. For small and medium size boards,
# this should work fine. For very large boards, we may need a 'global router' which divides
# the whole board into multiple bins, which then our 'local' router can manage.
#
# see thesis page 30, section 3.2.1 The Input Domain
#
# RUBBER-BAND BASED TOPOLOGICAL ROUTER, UNIVERSITY OF CALIFORNIA SANTA CRUZ, Tal Dayan 1997
#
# https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=91ce7726d0b103db47ab5db433ed75b538e6e7f8
# 
# This is the Nim implementation of the initial Ruby version from 2012
#
# v0.1 2023-MAR-10
#
# c 2012 - 2032 Dr. Stefan Salewski
#
# NOTE: we should move all the tiny helper procs in a separate module, together with minmax
#
import std/[tables, sets, hashes, sequtils, heapqueue, random, strutils, times]
from math import `^`, hypot
from std/os import paramCount, paramStr
from std/algorithm import sortedByIt
import itertools
import rtree
import minmax
import gintro/[cairo]

proc ego(x: varargs[string, `$`]) =
  for el in x:
    stdout.write(el & " ")
  stdout.write('\n')
  stdout.flushfile

proc isEven(i: int): bool =
  (i and 1) == 0

proc isOdd(i: int): bool =
  (i and 1) != 0

# may cause trouble?  
#proc `<`(a, b: pointer): bool =
#  cast[int](a) < cast[int](b)

template times(n: int; actions: untyped) =
  for _ in 0 ..< n:
    actions

type # our 2d vector type
  V2 = tuple
    x, y: float

proc hyp2(a, b: V2): float =
  (a.x - b.x) ^ 2 + (a.y - b.y) ^ 2

type
  Layer = int8

type
  ViaX = object # the obstacles, will expand later
    x, y, r: float # position and radius

# bounding box of circle for rtree
proc vbox(c: ViaX): Box[2, float] =
  result[0].a = c.x - c.r
  result[0].b = c.x + c.r
  result[1].a = c.y - c.r
  result[1].b = c.y + c.r

type
  Tree = rtree.RStarTree[8, 2, float, ViaX]

type
  Segment = ref object
    x1, y1, x2, y2: float
    intersectingSegments: seq[Segment]
    layer: Layer
    isActive: bool # maybe use increasing int to avoid initialization to false? May cover fresh as well

type
  SegTuple = tuple
    a, b: Segment

type
  SortedSegTuple = tuple
    a, b: Segment

# we should never have two segments with identical coordinates but different memory location!
# so we can calculate the hash by address or by coordinates
# these hash() procs are really ugly
proc hash(v: Segment): Hash =
  var h: Hash = 0
  h = h !& addr(v[]).hash
  result = !$h

# Currently we make detour costs symmetric, c(a, b) = min(c(a, b), c(b, a))
# Does that make sense? Well maybe yes, when we route the final rubberbands
# always in increasing order of length. But we may change that later?
#
# sorted segment tuple
proc sst(t: SegTuple): SortedSegTuple =
  if cast[int](addr(t.a[])) < cast[int](addr(t.b[])):
    t
  else:
    (t.b, t.a)

# pair pair detour costs
type
  PPDC = TableRef[(Segment, Segment), float]

const
  DefaultPPDC = system.Inf

proc `[]`(self: PPDC; a, b: Segment): float =
  self.getOrDefault(sst((a, b)), DefaultPPDC)

proc `[]`(self: PPDC; t: SegTuple): float =
  self.getOrDefault(sst(t), DefaultPPDC)

proc `[]=`(self: PPDC; a, b: Segment; v: float) =
  self.`[]=`(sst((a, b)), v)

proc `[]=`(self: PPDC; t: SegTuple; v: float) =
  self.`[]=`(sst(t), v)

proc newSegment(a, b: (float, float)): Segment =
  Segment(x1: a[0], y1: a[1], x2: b[0], y2: b[1])

proc newSegment(x1, y1, x2, y2: float): Segment =
  Segment(x1: x1, y1: y1, x2: x2, y2: y2)

type
  Style = int # fix later

type
  Terminal = ref object
    name: string
    netName: string
    style: Style
    x, y: float # location
    layers: set[Layer] # range where it exists
    friend: Terminal # for prim()
    dist: float = Inf # for prim()

proc newTerminal(name, netName: string; style: Style; x, y: float; layers: set[Layer]): Terminal =
  Terminal(name: name, netName: netName, x: x, y: y, layers: layers, style: style)

type
  Node = ref object of RootRef
    x, y: float # note: via-nodes may not really need the x, y coordinates
    next: seq[Node]
    prev: Node

proc hash(v: Node): Hash =
  var h: Hash = 0
  h = h !& addr(v[]).hash
  result = !$h

type
  VNode = ref object of Node # via node
    layer: set[Layer]

proc newVNode(x, y: float; layer: set[Layer]; next: seq[Node]): VNode =
  VNode(x: x, y: y, layer: layer, next: next)

type
  SNode = ref object of Node # start node
    pads: set[Layer]

proc newSNode(x, y: float; pads: set[Layer]): SNode =
  SNode(x: x, y: y, pads: pads)

type
  FNode = ref object of Node # forward node 
    layer: Layer

proc newFNode(x, y: float; layer: Layer; next: seq[Node]): FNode =
  FNode(x: x, y: y, layer: layer, next: next)

type
  TNode = ref object of Node # terminal node
    pads: set[Layer]

proc newTNode(x, y: float; pads: set[Layer]): TNode =
  TNode(x: x, y: y, pads: pads)

type
  Input_2Net = ref object
    t1: Terminal
    t2: Terminal
    t1Ext: float # what is this?
    t2Ext: float

proc newInput2Net(t1, t2: Terminal): Input2Net =
  Input2Net(t1: t1, t2: t2)

type
  Output_2Net = ref object
    viaPositions: seq[(float, float)] # array of x, y pairs, along a path from startNode to endNode
    viaThickness: float
    viaClearance: float
    viaCost: float = 3.0
    startNode: SNode
    endNode: TNode
    segmentList: seq[Segment]
    path: seq[Segment]
    ppdc: PPDC
    i2n: Input_2Net
    oldCost: float
    newCost: float
    layerCount: int

proc newOutput_2Net(startNode: SNode; endNode: T_Node; viaPositions: seq[(float, float)]; layerCount: int): Output_2Net =
  Output2Net(startNode: startNode, endNode: endNode, viaPositions: viaPositions, layerCount: layerCount)

proc findSegment(self: Output_2Net; x1, y1, x2, y2: float): Segment =
  for el in self.segmentList:
    if el.x1 == x1 and el.y1 == y1 and el.x2 == x2 and el.y2 == y2:
      return el
  assert false

# dummy for now
proc getViaPosition(x1, y1, x, y, x2, y2, viaSize, viaClearance: float): seq[(float, float)] =
  result.add((x, y))

proc buildAssignmentGraph(self: Output_2Net) = # path
  assert(self.segmentList.len == 0)
  assert(self.layerCount == 2) # for now
  assert(self.viaPositions.len > 0)
  assert(self.layerCount > 1)
  assert(self.startNode.pads * {self.layerCount.int8 .. int8.high} == {})
  assert(self.endNode.pads * {self.layerCount.int8 .. int8.high} == {})
  assert(self.startNode.pads * {0.int8 .. (self.layerCount - 1).int8} != {})
  assert(self.endNode.pads * {0.int8 .. (self.layerCount.int8 - 1.int8)} != {})
  let viaCount = self.viaPositions.len
  let layers = 0 .. (self.layerCount - 1)
  let colums = 0 .. (viaCount * 2) # F O F O F for viaCount == 2
  var vp = (self.startNode.x, self.startNode.y) & self.viaPositions

  var m = newSeqWith(self.layerCount, newSeq[Node](viaCount * 2 + 1))
  var x, y: float
  var i = vp.high
  while i >= 0:
    var k = i
    while k <= vp.high:
      inc(k)
      if k > vp.high:
        self.segmentList.add(newSegment(vp[i], (self.endNode.x, self.endNode.y)))
      else:
        self.segmentList.add(newSegment(vp[i], vp[k]))
    dec(i)

  for i in colums: # from T back to S
    if i.isEven:
      (x, y) = vp.pop # pick current position
    for j in layers:
      var l: seq[Node] # possible paths
      if i.isEven: # forward
        var k = i + 1
        while k > 0:
          k -= 2
          if k == -1: # link forward node to T node
            if self.endNode.pads.contains(j.int8):
              l.add(self.endNode)
          else: # link to via node
            #assert m[j][k] != nil # may fail, as  m[j][k] is nil when path would not continue from it 
            if (let h = m[j][k]; h != nil):
              assert(h of VNode)
              l.add(h) # link to a reachable up/down node
        if l.len > 0: # only if path continues
          m[j][i] = newFNode(x, y, j.int8, l) # l is the nxt seq
      else: #up/down
        for k in layers:
          let h = m[k][i - 1]
          assert(h == nil or h of FNode)
          #assert h != nil # may fail as there may exist no forward node to endNode on this layer
          if (k != j) and (h != nil):
            l.add(h)
        if l.len > 0: # if path continues
          m[j][i] = newVNode(x, y, {j.int8}, l) # l is the nxt seq

  for j in layers:
    let h = m[j][^1]
    assert(h of FNode)
    assert h != nil
    if (h != nil) and self.startNode.pads.contains(j.int8):
      self.startNode.next.add(h)
  assert self.segmentList.filterIt(it.x1 == self.endNode.x or it.x2 == self.endNode.x).len > 0
  assert self.segmentList.filterIt(it.x1 == self.startNode.x or it.x2 == self.startNode.x).len > 0

proc pathCost(self: Output_2Net): float =
  var oldseg: Segment = self.path[0]
  for seg in self.path:
    if oldseg.layer != seg.layer:
      result += self.viaCost
    oldseg = seg
    for el in seg.intersectingSegments:
      if seg.layer == el.layer and el.isActive:
        result += self.ppdc[seg, el]

type
  NodeWrapper = object
    node: Node
    costs: float

proc `<`(a, b: NodeWrapper): bool = a.costs < b.costs

#https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
# minimize costs of path for a single Output_2Net
# sets newCost field for self
proc dijkstra(self: Output_2Net) =
  let s = self.startNode
  let t = self.endNode
  assert(s of SNode)
  assert(t of TNode)
  self.path.setLen(0)
  var q: HeapQueue[NodeWrapper]
  var c: Table[Node, float] # legacy from Ruby, avoids initialzation with Inf. We may use time/value node fields instead.
  q.push(NodeWrapper(node: s, costs: 0))
  c[s] = 0
  var u: Node
  while q.len > 0:
    let uu = q.pop
    if uu.costs != c[uu.node]:
      continue
    u = uu.node
    if u == t:
      break
    assert(c[u] != Inf)
    assert(u.next.len > 0)
    for v in u.next:
      var cost: float = c[u]
      if u of FNode:
        let seg = self.findSegment(u.x, u.y, v.x, v.y)
        for el in seg.intersectingSegments:
          if FNode(u).layer == el.layer and el.isActive:
            cost += self.ppdc[seg, el] # we may attach ppdc value directly to seg and avoid table
      else:
        assert(u of VNode or u of SNode) # or u of TNode
        if u != s: # if u of VNode
          cost += self.viaCost
      if cost < c.getOrDefault(v, system.Inf):
        q.push(NodeWrapper(node: v, costs: cost))
        c[v] = cost
        v.prev = u
  self.newCost = c[t]
  assert(t == TNode(u))
  var n = Node(t)
  while n != s:
    let p = n.prev
    if p of FNode:
      let seg = self.findSegment(p.x, p.y, n.x, n.y)
      seg.layer = FNode(p).layer
      self.path.add(seg)
    n = p
  assert((self.newCost - pathCost(self)).abs < 10.0) # should be equal

type
  Net_List = object
    name: string
    terminals: seq[Terminal]

type
  Via_Grid = Table[(float, float), (float, float)]

const Board_Size = 800

# layer assignment
type
  Assignment = object
    b1x, b1y, b2x, b2y: float # routing area, [bx1, by1] < [bx2, by2]
    minViaSize, maxViaSize: float
    numLayers: int
    rstyles: int # dummy
    inputNets: Table[string, seq[Terminal]]
    input_2nets: seq[Input_2Net]
    output_2nets: seq[Output_2Net]
    allSegmentList: seq[Segment]
    ppdc: PPDC
    rt: Tree
    pcbBoard: int # dummy for now
    image: cairo.Surface
    pic: cairo.Context
    maxExtent: float
    rand: random.Rand
    seed: int64

proc initAssignment(numLayers: int; minViaSize, maxViaSize: float; b1x, b1y, b2x, b2y: float): Assignment = #; rt: Tree; pcbBoard: int) =
  result = Assignment(numLayers: numLayers, minViaSize: minViaSize, maxViaSize: maxViaSize, b1x: b1x, b1y: b1y, b2x: b2x, b2y: b2y)
  assert(numLayers > 1)
  result.ppdc = new PPDC
  result.rt = newRStarTree[8, 2, float, ViaX]()
  result.image = cairo.imageSurfaceCreate(Format.argb32, Board_Size, Board_Size)
  result.pic = newContext(result.image)
  result.maxExtent = Board_Size.float / ([b2x - b1x, b2y - b1y].max)
  result.pic.scale(result.maxExtent, result.maxExtent)
  result.pic.translate(-b1x, -b1y)
  result.pic.setSource(0.8, 0.8, 0.8)
  result.pic.paint

proc savePicture(self: Assignment) =
  discard self.image.writeToPng("LApic.png")

#     a
#    ^
#   /
# o/--------> b
#
proc crossProduct(ax, ay, bx, by, ox, oy: float): float =
  (ax - ox) * (by - oy) - (ay - oy) * (bx - ox)

proc cp(ax, ay, bx, by, ox, oy: float): bool =
  (ax - ox) * (by - oy) < (ay - oy) * (bx - ox)

#         d
#        /
#  a-------------b
#      /
#     /
#    c
proc segmentSegmentIntersection(ax, ay, bx, by, cx, cy, dx, dy: float): bool =
  if ((cx == ax) and (cy == ay)) or ((dx == ax) and (dy == ay)) or ((cx == bx) and (cy == by)) or ((dx == bx) and (dy == by)):
    return false
  (cp(bx, by, cx, cy, ax, ay) != cp(bx, by, dx, dy, ax, ay)) and (cp(dx, dy, ax, ay, cx, cy) != cp(dx, dy, bx, by, cx, cy))

#      (c)
#     /
#    /     (p)
#   /
# (b)
# see http://www.geometrictools.com/
#
proc distanceLineSegmentPointSquared(bx, by, cx, cy, px, py: float): float =
  let mx = cx - bx
  let my = cy - by
  var hx = px - bx
  var hy = py - by
  let t0 = (mx * hx + my * hy) / (mx ^ 2 + my ^ 2)
  if t0 <= 0:
    discard
  elif t0 < 1:
    hx -= t0 * mx
    hy -= t0 * my
  else:
    hx -= mx
    hy -= my
  return hx ^ 2 + hy ^ 2

# we will clean this up later when we work with a real PCB board
proc generateViaPositions(self: Assignment; x1, y1, x2, y2: float; viaT: float; viaC: float): seq[(float, float)] =
  var viaCount = 5
  if math.hypot(x2 - x1, y2 - y1) < 1e5:
    viaCount = 2
  var viaList: seq[(float, float)]
  var dx = (x2 - x1) / (viaCount + 1).float
  var dy = (y2 - y1) / (viaCount + 1).float
  var x = x1
  var y = y1
  var vs = self.maxViaSize * 0.5
  for i in 0 ..< viaCount:
    self.pic.setSource(1, 1, 1, 1)
    self.pic.setLineWidth(500)
    var vp: seq[(float, float)] = getViaPosition(x, y, x + dx, y + dy, x + dx + dx, y + dy + dy, viaT, viaC)
    vp = @[(x + dx, y + dy)]
    for el in vp:
      self.pic.newSubPath
      self.pic.arc(el[0], el[1], 1500, 0, math.TAU)
      self.pic.stroke
    x += dx
    y += dy
    let x1 = x - vs
    let y1 = y - vs
    let x2 = x + vs
    let y2 = y + vs
    if self.rt.search(vbox(ViaX(x: 0.0, y: 0.0, r: 1.0))).len > 0:
      echo "isconflict"
    else:
      echo "noconflict"
    when false: #if vp.len == 0:
      echo "pech"
    else:
      echo "glueck"
      viaList.add(vp[0])
      if false: #self.rt.intersects(vp[0][0] - vs, vp[0][1] - vs, vp[0][0] + vs, vp[0][1] + vs).len > 0:
        self.pic.setSource(1, 1, 0, 1)
        self.pic.newSubPath
        self.pic.arc(vp[0][0], vp[0][1], 2000, 0, math.TAU)
        self.pic.stroke
  if viaList.len == 0: #|| !@rt.intersects?(viaList[0] - vs, viaList[1] - vs, viaList[0] + vs, viaList[1] + vs).empty?
    assert false
    dx = (x2 - x1)
    dy = (y2 - y1)
    x = x1 + dx * 0.5
    y = y1 + dy * 0.5
    dx *= 0.1
    dy *= 0.1
    for _ in 1 .. 9:
      1e4.int.times:
        var vp: seq[(float, float)] = getViaPosition(x1, y1, x + rand(1.0) * dx, y + rand(1.0) * dy, x2, y2, self.minViaSize,
            self.maxViaSize)
        if vp.len > 0:
          self.pic.newSubPath
          self.pic.arc(vp[0][0], vp[0][1], 1200, 0, math.TAU)
          self.pic.stroke
          return @[vp[0]]
      #puts "no space", x, y
      dx *= 2
      dy *= 2
    assert false #fail
  else:
    return viaList

type
  Container = object
    u: Node
    d: float

# http://en.wikipedia.org/wiki/Prim'sAlgorithm
# http://de.wikipedia.org/wiki/AlgorithmusVon_Prim
proc prim(vertices: var seq[Terminal]): seq[Terminal] =
  var last = vertices.pop # arbitrary start point, assume that we have at least one available
  while vertices.len > 0: # while there are more, still unconnected points available
    var nearest = Inf
    var pos = -1
    for p, v in vertices: # all vertices that are not yet part of the tree
      let d = (v.x - last.x) ^ 2 + (v.y - last.y) ^ 2 # squared distance
      if d < v.dist: # update distances, as last is a new point in tree
        v.dist = d
        v.friend = last
      if v.dist < nearest: # remember nearest point
        nearest = v.dist
        pos = p
    last = vertices[pos] # and pick nearest,
    result.add(last) # add it to forest and
    vertices.del(pos) # delete it from still unconnected vertex set

proc inclde(s: seq[Terminal]; el: Terminal): bool =
  s.find(el) >= 0

proc delete(s: var seq[Input_2Net]; el: Input_2Net) =
  let p = s.find(el)
  assert(p >= 0)
  system.delete(s, p)

proc genInput_2nets(self: var Assignment) =
  for v in mvalues(self.inputNets):
    for el in prim(v):
      self.input_2nets.add(newInput2Net(el, el.friend))
#[ legacy from Ruby. For what do we need it?
    for n in self.input_2nets:
      for t in [n.t1, n.t2]:
        var numTerminals = 0
        var terminals: seq[Terminal]
        terminals.add(t)
        while true:
          var nets = self.input_2nets.filterIt(terminals.inclde(it.t1) or terminals.inclde(it.t2))
          nets.delete(n)
          for el in nets:
            terminals.add(el.t1)
            terminals.add(el.t2)
          terminals = terminals.deduplicate
          let l = terminals.len
          if l == numTerminals:
            break
          numTerminals = l
        let m = terminals.maxValueByIt(math.hypot(it.x - t.x, it.y - t.y))
        let l = math.hypot(m.x - t.x, m.y - t.y)
        if t == n.t1:
          n.t1Ext = l
        else:
          n.t2Ext = l
]#

# replaced by itertools.windowed
iterator eachCons[T](a: openarray[T]; s: static[int]): array[s, T] {.inline.} =
  var result: array[s, T] # iterators have no default result variable
  var i = 0
  while i < len(a):
    for j, x in mpairs(result):
      x = a[(i + j) mod len(a)]
    yield result
    inc(i)

proc getVias(self: Assignment) =
  var v: seq[(float, float)]
  for el in self.output_2nets:
    for s in el.path:
      if s.layer == 0:
        v.add((s.x2, s.y2))
        v.add((s.x1, s.y1))
  self.pic.setSource(0, 0, 1, 0.5)
  for el in v:
    self.pic.newSubPath
    self.pic.arc(el[0], el[1], 1000, 0, math.TAU)
    self.pic.stroke

proc fixPaths(self: Assignment) = # only PCB related
  for el in self.output_2nets:
    for h in el.path.windowed(2):
      var (a, b) = (h[0], h[1])
    #el.path.eachCons(2){|a, b|
      if not (b.x2 == a.x1 and b.y2 == a.y1):
        #puts a.x1, a.x2 , b.x1, b.x2
        assert false
      #let (x, y) = self.pcbBoard.getViaPosition(b.x1, b.y1, b.x2, b.y2, a.x2, a.y2, self.minViaSize, self.maxViaSize)[0]
      var x, y: float
      (x, y) = getViaPosition(b.x1, b.y1, b.x2, b.y2, a.x2, a.y2, self.minViaSize, self.maxViaSize)[0]
      b.x2 = x
      a.x1 = x
      b.y2 = y
      a.y1 = y
      #self.pcbBoard.insertVia(x, y, el.viaThickness, el.viaClearance)

proc drawPaths(self: Assignment) =
  self.pic.setLineWidth(1000)
  for el in self.output_2nets:
    var col = ([1, 0, 0].permutations.toSeq & [1, 1, 0].permutations.toSeq).deduplicate # - [[1, 0, 0]]
    col.delete(col.find([1, 0, 0]))
    var colorIndex = rand(5 - 1)
    for s in el.path:
      if s.layer == 0:
        self.pic.setSource(col[colorIndex][0].float, col[colorIndex][1].float, col[colorIndex][2].float, 0.3)
      else:
        self.pic.setSource(col[colorIndex][0].float, col[colorIndex][1].float, col[colorIndex][2].float, 1)
      self.pic.moveTo(s.x1, s.y1)
      self.pic.lineTo(s.x2, s.y2)
      self.pic.stroke
      self.pic.setSource(0, 0, 0, 1)
      self.pic.newSubPath
      self.pic.arc(s.x1, s.y1, 5, 0, math.TAU)
      self.pic.newSubPath
      self.pic.arc(s.x2, s.y2, 5, 0, math.TAU)
      self.pic.stroke
    self.pic.setSource(0.5, 0.5, 0.5, 1)
    if el.startNode.pads == {0.int8}: #(0 .. 0):
      self.pic.setSource(1, 1, 1, 1)
    elif el.startNode.pads == {1.int8}: # (1 .. 1):
      self.pic.setSource(0, 0, 0, 1)
    self.pic.newSubPath
    self.pic.arc(el.startNode.x, el.startNode.y, 5, 0, math.TAU)
    self.pic.stroke
    self.pic.setSource(0.5, 0.5, 0.5, 1)
    if el.endNode.pads == {0.int8}: #(0 .. 0):
      self.pic.setSource(1, 1, 1, 1)
    elif el.endNode.pads == {1.int8}: # (1 .. 1):
      self.pic.setSource(0, 0, 0, 1)
    self.pic.newSubPath
    self.pic.arc(el.endNode.x, el.endNode.y, 5, 0, math.TAU)
    self.pic.stroke

proc drawInput_2nets(self: Assignment) =
  self.pic.setSource(0, 0, 0, 1)
  self.pic.setLineWidth(200)
  for el in self.input_2nets:
    var col = ([1, 0, 0].permutations.toSeq & [1, 1, 0].permutations.toSeq).deduplicate # - [[1, 0, 0]]
    col.delete(col.find([1, 0, 0]))
    let h = el.t1.netName.parseInt mod 5
    self.pic.moveTo(el.t1.x, el.t1.y)
    self.pic.lineTo(el.t2.x, el.t2.y)
    self.pic.stroke
    self.pic.newSubPath

proc addInputTerminal(self: var Assignment; terminal: Terminal) =
  var n = terminal.netName
  if self.inputNets.hasKey(n):
    var h = self.inputNets[n]
    self.inputNets[n].add(terminal)
  else:
    self.inputNets[n] = @[terminal]

proc genTestInputNets(self: var Assignment; num: int) =
  for j in 0 ..< num:
    let i = 2 + rand(4 - 1) # create min 2, max 5 terminals for this net
    i.times:
      let x = self.b1x + rand(self.b2x - self.b1x)
      let y = self.b1y + rand(self.b2y - self.b1y)
      let t = newTerminal($i, $j, 1, x, y, [{0.int8}, {0.int8, (self.numLayers - 1).int8}, {(self.numLayers - 1).int8}][rand(3 - 1)])
      self.addInputTerminal(t)

proc genOutput_2nets(self: var Assignment) =
  for el in self.input_2nets:
    let s = newSNode(el.t1.x, el.t1.y, el.t1.layers)
    let t = newTNode(el.t2.x, el.t2.y, el.t2.layers)
    let viaT = 1.0 #self.rstyles[el.t1.style].viaDiameter #* 0.5
    let viaC = 1.0 #self.rstyles[el.t1.style].viaClearance #* 0.5
    var vp = self.generateViaPositions(el.t1.x, el.t1.y, el.t2.x, el.t2.y, viaT, viaC)
    var n = newOutput_2Net(s, t, vp, self.numLayers)
    n.i2n = el
    n.viaClearance = 1 * viaC
    n.viaThickness = 1 * viaT
    n.buildAssignmentGraph
    self.output_2nets.add(n)

proc genAllSegmentList(self: var Assignment) =
  for el in self.output_2nets:
    for x in el.segmentList:
      self.allSegmentList.add(x)

#        /d
# a-------------s-----------b
#      /si
#     /c
#
# detour of s when si is active on the same layer
proc gen_PPDC(self: var Assignment) =
  for o2n in self.output_2nets:
    for s in o2n.segmentList:
      var (ax, ay) = (s.x1, s.y1)
      var (bx, by) = (s.x2, s.y2)
      for si in s.intersectingSegments:
        var (cx, cy) = (si.x1, si.y1)
        var (dx, dy) = (si.x2, si.y2)
        let cD = math.hypot(dx - cx, dy - cy)
        let aC = math.hypot(cx - ax, cy - ay)
        let aD = math.hypot(dx - ax, dy - ay)
        let bC = math.hypot(cx - bx, cy - by)
        let bD = math.hypot(dx - bx, dy - by)
        var d1 = aC + aD - cD
        #if ax == o2n.i2n.t1.x and ay == o2n.i2n.t1.y: # currently we are unable to remember the purpose
        #  d1 += o2n.i2n.t1Ext
        var d2 = bC + bD - cD
        #if bx == o2n.i2n.t2.x and by == o2n.i2n.t2.y:
        #  d2 += o2n.i2n.t2Ext
        let d = self.ppdc[s, si]
        self.ppdc[s, si] = [d, d1, d2].min # why min, why not max? which seg do we route first?

proc findIntersectingSegmensts(self: Assignment) =
  for o2n in self.output_2nets:
    for si in o2n.segmentList:
      for sj in self.allSegmentList:
        if segmentSegmentIntersection(si.x1, si.y1, si.x2, si.y2, sj.x1, sj.y1, sj.x2, sj.y2):
          si.intersectingSegments.add(sj)

proc initOutput_2nets(self: Assignment) =
  for o2n in self.output_2nets:
    o2n.ppdc = self.ppdc

proc routeOutput_2netsFirstTime(self: var Assignment) =
  for el in self.output_2nets.sortedByIt(-hyp2((it.i2n.t1.x, it.i2n.t1.y), (it.i2n.t2.x, it.i2n.t2.y))): # long nets first, really!
    el.dijkstra
    for x in el.path:
      x.isActive = true
  10.times:
    var sum = 0.0
    for el in self.output_2nets:
      el.oldCost = el.pathCost
      sum += el.oldCost
    echo "sum: ", sum
    for x in self.output_2nets.sortedByIt(-it.oldCost):
      if x.oldCost < 10.0:
        break
      for el in x.path:
        el.isActive = false
      x.dijkstra
      for el in x.path:
        el.isActive = true

proc initSeed(r: var Assignment) =
  var seed: int64
  if paramCount() == 1:
    seed = strutils.parseInt(paramStr(1))
  if seed == 0:
    let now = getTime()
    seed = now.toUnix * 1_000_000_000 + now.nanosecond
    seed = seed mod 100
  r.rand = initRand(seed)
  echo "Random seed: ", seed
  r.seed = seed

when isMainModule:
  var l = initAssignment(2, 1000, 1000, 0, 0, 400000, 400000)
  l.initSeed
  l.genTestInputNets(16)
  l.genInput_2nets
  l.drawInput_2nets
  l.genOutput_2nets
  l.genAllSegmentList
  l.findIntersectingSegmensts
  l.gen_PPDC
  l.initOutput_2nets
  l.routeOutput_2netsFirstTime
  l.drawPaths
  l.getVias
  l.savePicture

#[
2-Net Assignment Graph, similar to Figure 42

  /- |-> F -> O -\    l1
 / - |-> F -> O - \   l2
S -- O   F -> O -- T  l3
 \ - |-> F -> O - /   l4
  \- |-> F -> O -/    l5
         \--- (to next via node)

Path starts at terminal S. Then Via nodes and Forward nodes alternate.
Each forward node has edges to all via nodes at the right.
Each via node has paths to the next Forward nodes at the right, excluding the
forward node on the same layer.
]#

# 805 lines
