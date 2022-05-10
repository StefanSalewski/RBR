# sed -E 's/_([a-z])/\U\1/g' router.nim.bak > router.nim
# nimpretty --maxLineLen:130 router.nim
# file: router.rb
# note: source code is indented with tabs, tab-width=2
#
# A rubberband topological router based on the region concept mentioned in
# Tal Dayan's PhD thesis and other papers.
# See http://www.delorie.com/archives/browse.cgi?p=geda-user/2015/10/11/08:56:15
#
# c Stefan Salewsk, mail@ssalewski.de
# License GPL
# Version 0.21 29-DEC-2015
#
# For testing with random points, call
# ruby router.rb
# or ruby router.rb seed
# for reproduceable results
#
# ruby pcbtr.rb
# will route the t.pcb file, currently component side only
#
# Data type of coordinates
# ------------------------
# Generally integer data type should make our life easierer, but then we have to be careful
# when float datatype is mixed in by math operations. Special care is necessary when we use
# coordinates as Hash keys -- float and integer are of course different keys.
# Current default unit in PCB file format is 0.01 mil, generally in combination with integer
# numbers. (Internal unit in PCB program is nm.)
# For now we use 0.01 mil as our general coordinates. (For Ruby performance it may be a good idea
# to use only integers less than 2^30 in magnitude?)
#
# Markers used:
# TODO: needs improving
# UGLY: we should remove or at least carefully check this...
#
# Used termes:
# traceWidth: i.e 10mil; we should avoid unprecise PCB term thickness
# traceClearance: copper free distance to next element -- in PCB file format there is a factor of 2
# viaDiameter: outer diameter of copper annulus; avoid unprecise term size
# viaDrillDiameter:
# viaClearance: copper free distance to next elemment
# viaMaskDiameter:
#
# we use the term "routing style" to name a set of {traceWidth, traceClearance, via...}
#

import random
import times
from math import `^`, round, arctan2, hypot
from os import paramCount, paramStr
from strutils import parseInt
from sequtils import filter, mapIt, anyIt, applyIt, keepItIf, filterIt, delete, toSeq, deduplicate
from algorithm import sort, sorted, sortedByIt, reverse, reversed
import tables
import sets
import combinatorics
import hashes
import gintro/[cairo]
from itertools import chunked, windowed
import heapqueue
import maxby
import salewski
#import cdt/[dt, vectors, vertices, edges, types]
import cdt2/[dt, vectors, vertices, edges, types]
#import "../quickhulldisk/quickhulldisk"
#import "../quickhulldisk/convexhullofdisks"
#import "../quickhulldisk/circulardisk2d"
import quickhulldisk/[quickhulldisk, convexhullofdisks, circulardisk2d]

const
  initVector = initVector3

const
  NilInt = low(int)
  NilFloat = 1e300#system.NaN

const
  glob = 0 # global variable for debugging and statistics

#@@one = 1
#@@two = 2

# Some global constants -- we try to use integer range less than 2 ** 30
# Note: Our internal unit is 0.01 mil
const
  Maximum_Board_Diagonal = (2 ^ 30 - 2 ^ 24).float # something like our own Infinity
  MBD = Maximum_Board_Diagonal
  Average_Via_Diameter = 50_00 # 50 mil -- we may determine that value from actual PCB board data
  AVD = Average_Via_Diameter
  Average_Trace_Width = 10_00 # 10 mil -- we may determine that value from actual PCB board data
  ATW = Average_Trace_Width
  Board_Size = 800 # cairo PNG picture

# the following constants are used for tests with random numbers, not for real PCB board
  PCB_Size = 140000 # size of our set of random vertices
  Points = 64 # terminal count for test
  Pin_Radius = 2000
  Trace_Width = 1200
  Clearance = 800
  MinCutSize = 6000

var
  Global_Rand: Rand

proc `<=>`(a, b: float): int =
  if a < b:
    -1
  elif a > b:
    1
  else:
    0

proc isEven(i: int): bool =
  (i and 1) == 0

proc isOdd(i: int): bool =
  (i and 1) != 0

proc minmax(a, b: int): (int, int) =
  if a < b:
    (a, b)
  else:
    (b, a)

proc minmax(a, b: float): (float, float) =
  if a < b:
    (a, b)
  else:
    (b, a)

proc failIf(b: bool) =
  assert(not b)

iterator countup(a, b, step: float): float =
  assert step > 0
  var res = a
  while res <= b:
    yield res
    res += step

iterator itemsReversed[T: not char](a: openArray[T]): T =
  ## Iterates over each item of `a` backwards.
  var i = a.len
  while i > 0:
    dec(i)
    yield a[i]

proc shift(s: var seq[int]): int =
  result = s[0]
  s.delete(0)

# from salewski module
# iterator xclusters*[T](a: openarray[T]; s: static[int]): array[s, T] {.inline.} =
iterator eachCons*[T](a: openarray[T]; s: static[int]): array[s, T] {.inline.} =
  var result: array[s, T] # iterators have no default result variable
  var i = 0
  while i < len(a):
    for j, x in mpairs(result):
      x = a[(i + j) mod len(a)]
    yield result
    inc(i)

# from Mr. Behrends
#iterator permutations*[T](s: openarray[T]): seq[T] =
iterator permutations*[T](s: openarray[T]): seq[T] =
  ## Enumerates all possible permutations of `s`. Example:
  ##
  ## .. code-block:: nimrod
  ##   for p in permutations(@[1,2,3]):
  ##
  ## ...generates this output:
  ##
  ## .. code-block::
  ##   @[1, 2, 3]
  ##   @[2, 1, 3]
  ##   @[1, 3, 2]
  ##   @[2, 3, 1]
  ##   @[3, 2, 1]
  ##   @[3, 1, 2]
  let n = len(s)
  var pos = newSeq[int](n)
  var current = newSeq[T](n)
  for i in 0..n-1:
    pos[i] = i
  while true:
    for i in 0..n-1:
      current[i] = current[pos[i]]
      current[pos[i]] = s[i]
    yield current
    var i = 1
    while i < n:
      pos[i] -= 1
      if pos[i] < 0:
        pos[i] = i
        i += 1
      else:
        break
    if i >= n:
      break

# Net connecting two terminals (2Net)
type
  NetDesc = object
    #@@xid = 0
    t1Name: string
    t2Name: string # name of terminals
    styleName: string
    traceWidth: float
    traceClearance: float
    xid: int
    pri: int # used for sorting by length -- poor mans net ordering
    flag: int # used for sorting of attached nets

proc newNetDesc(t1Name, t2Name: string; traceWidth: float = Trace_Width; traceClearance: float = Clearance): NetDesc =
  var n = NetDesc()
  var xid {.global.}: int
  inc(xid)
  n.xid = xid
  n.pri = 0
  n.t1Name = t1Name
  n.t2Name = t2Name
  n. traceWidth = traceWidth
  n. traceClearance = traceClearance
  return n

type
  NetDescList = seq[NetDesc]

# Incident or attached net of a terminal

# Terminal
var VertexClassID = 0
var VertexClusterID = 0

type
  # Terminal
  XVertex = ref object of Vertex
    #@@xid = @@cid = 0
    xid: int # general unique xid number
    cid: int # cluster xid; -1 for plain pins, nonnegativ values if vertex is part of a pad/cluster
    visFlag: int # for debugging, graphical color mark
    core: float # outer copper of pin itself, without attached traces
    radius: float # outer copper of outermost attached trace, equal to core when no attached nets exist
    separation: float # outer clearance of pin itself or of outermost attached trace
    neighbors: seq[XVertex] # XVertex/Terminal, the neighbors in the delaunay triangulation
    incidentNets: seq[Step] # Step, nets incident to this terminal
    attachedNets: seq[Step] # Step, nets attached to this terminal
    name: string # name of the Terminal, i.e. U7_3 -- pin 3 of IC U7
    tradius: float
    trgt: bool # temporary data
    outer: bool # temporary data for routing,
    lrTurn: Step # later copied to step
    via: bool # vertex is a via
    numInets: int # how many incident nets should this vertex get
    x, y: float
    vc, vt: float
    shash: Table[(XVertex, XVertex), seq[Step]]

# Incident or attached net of a terminal
  Step = ref object
    xid: int # xid of this net
    netDesc: Net_Desc
    vertex: XVertex # the terminal we are attached or incident to
    prev: XVertex
    next: XVertex # terminal
    pstep: Step
    nstep: Step # previous and next step
    a, b, g: int # for sorting, a few may be obsolete
    dir, d: float
    radius: float # radius of arc
    score: float # for sorting attached nets of a terminal by angle
    index: int # for sorting
    #`ref`{.cursor.}: Step # also for sorting
    `ref`: Step # also for sorting
    rgt: bool # tangents of terminal for this step -- left or right side in forward direction
    outer: bool # do we use the outer lane at this terminal
    xt: bool # do tangents cross each other -- if so we can collapse this concave step
    lrTurn: bool # left or right turn

#   \|/       \|/
#    |        /\
#    |        | |
#   _|/      _| |/
#    |\       | |\
# when we route a net, we split regions along the path in left and right region.
# so new paths can not cross this path any more.
# problem: first and last terminal.
# Current solution: Use a hash to store forbidden paths for these terminals
#
type
  Region = ref object
    vertex: XVertex
    neighbors: seq[Region]
    incident: bool
    outer: bool
    g: float
    ox: float
    oy: float
    rx: float
    ry: float
    lrTurn: bool
    idirs: seq[(float, float)]
    odirs: seq[(float, float)]

proc newXVertex(x: float = 0, y: float = 0, r: float = Pin_Radius, c: float = Clearance): XVertex =
  var v = XVertex()
  v.x = x
  v.y = y
  v.numInets = 0
  v.via = false
  v.tradius = 0
  v.visFlag = 0
  v.xid = VertexClassID
  v.cid = -1
  VertexClassID += 1
  v.radius = r
  v.core = r
  v.separation = c
  v.name = ""
  return v


# proc vertexAllocProc: XVertex = # was working with older compiler versions
proc vertexAllocProc: Vertex = # needed for compiler version >= 1.6
  result = newXVertex()

proc hash(vt: Region): Hash =
  var h: Hash = 0
  h = h !& addr(vt[]).hash
  result = !$h

proc hash(v: XVertex): Hash =
  var h: Hash = 0
  h = h !& addr(v[]).hash
  result = !$h

proc hash(v: Step): Hash =
  var h: Hash = 0
  h = h !& addr(v[]).hash
  result = !$h

proc `-`*[T](a, b: openArray[T]): seq[T] =
  let s = b.toHashSet
  result = newSeq[T](a.len)
  var i = 0
  for el in a:
    if el notin s:
      result[i] = el
      inc(i)
  result.setLen(i)

proc `-=`*[T](a: var seq[T]; b: openArray[T]) =
  let s = b.toHashSet
  var i = 0
  var j = 0
  while i < a.len:
    if a[i] notin s:
      a[j] = a[i]
      inc(j)
    inc(i)
  a.setLen(a.len - (i - j))

proc newStep(prev, nxt: XVertex; xid: int): Step =
  var s = Step()
  s.prev = prev
  s.next = nxt
  s.xid = xid
  s.radius = 0 # default for incident net
  s.outer = false
  return s

#     b
#    ^
#   /
# o/--------> a
#
proc booleanReallySmartCrossProduct2dWithOffset(a, b, o: XVertex): bool =
  var
    ax = a.x
    ay = a.y
    bx = b.x
    by = b.y
    ox = o.x
    oy = o.y
  failIf(ax == bx and ay == by) # undefined result, we should raise an exeption!
  ax -= ox
  ay -= oy
  bx -= ox
  by -= oy
  failIf((ax == 0 and ay == 0) or (bx == 0 and by == 0)) # zero length should not occur
  let p = ax * by - ay * bx
  if p != 0:
    p > 0
  else:
    if ax != bx:
      ax < bx
    else:
      ay < by # straight line -- ensure arbitrary but well defined result

proc xbooleanReallySmartCrossProduct2dWithOffset(a, b, o: Region): bool =
  var
    ax = a.vertex.x + a.ox
    ay = a.vertex.y + a.oy
    bx = b.vertex.x + b.ox
    by = b.vertex.y + b.ox
    ox = o.vertex.x
    oy = o.vertex.y
  failif(ax == bx and ay == by) # undefined result, we should raise an exeption!
  ax -= ox
  ay -= oy
  bx -= ox
  by -= oy
  failif((ax == 0 and ay == 0) or (bx == 0 and by == 0)) # zero length should not occur
  let p = ax * by - ay * bx
  if p != 0:
    p > 0
  else: # straight line -- ensure arbitrary but well defined result
    if ax != bx:
      ax < bx
    else:
      ay < by

# same as above for plain numbers -- used in qbors()
proc booleanReallySmartCrossProduct2d(ax, ay, bx, by: float): bool =
  failif(ax == bx and ay == by) # undefined result, we should raise an exeption!
  failif((ax == 0 and ay == 0) or (bx == 0 and by == 0)) # zero length should not occur
  let p = ax * by - ay * bx
  if p != 0:
    p > 0
  else: # straight line -- ensure arbitrary but well defined result
    if ax != bx:
      ax < bx
    else:
      ay < by

type
  Tex = object # plain (temporary) terminal (verTex)
    x: float
    y: float

proc newTex(x, y: float): Tex =
    result.x = x
    result.y = y

proc resetVertexClass =
  discard
  #@@xid = @@cid = 0

proc beginNewCluster = # class method!
  discard
  # @@cid += 1

proc addToCurrentCluster(v: XVertex) =
   v.cid = VertexClusterID

proc xy(v: XVertex): (float, float) =
    return (v.x, v.y)

  # UGLY:
proc resetInitialSize(v: XVertex) =
  v.radius = v.core
  v.separation = Clearance

  # UGLY: may be obsolete -- at least it is only an estimation
proc resize(v: XVertex) =
  v.resetInitialSize
  for step in items(v.attachedNets):
    let net = step.netDesc
    let traceSep = [v.separation, net.traceClearance].max
    v.radius += traceSep + net.traceWidth
    step.radius = v.radius - net.traceWidth / 2
    v.separation = net.traceClearance

# UGLY:
# assume worst case order --> max radius
proc unfriendlyResize(v: XVertex) =
    let cl = v.attachedNets.mapIt(it.netDesc.traceClearance)
    v.radius = v.core
    for n in v.attachedNets:
      v.radius += n.netDesc.traceWidth
    var s = 0.0
    for p in cl.permutations:
      for c in p.eachCons(2):
        s += (c.max)
    v.radius += s
    #v.radius += cl.permutation.map{|el| (el.push(v.separation))}.map{|el| s = 0; el.eachCons(2){|a, b| s += [a,b].max}; s}.max
    #v.separation = cl.push(v.separation).max
    v.separation = max(cl & v.separation)

# UGLY: may be obsolete -- at least it is only an estimation
proc update(v: XVertex; s: Step) =
  let net = s.netDesc
  let traceSep = [v.separation, net.traceClearance].max
  v.radius += traceSep + net.traceWidth
  s.radius = v.radius - net.traceWidth / 2
  v.separation = net.traceClearance

  # UGLY: returns step -- may become obsolete
proc net(v: XVertex; xid: int): Step =
  for s in v.incidentNets:
    if s.xid == xid:
      return s
  for s in v.attachedNets:
    if s.xid == xid:
      return s
  #return nil

# UGLY: delete step -- currently we need this, but we should try to avoid it, at least the expensive resize operation
proc newDeleteNet(v: XVertex; step: Step) =
  v.incidentNets.keepItIf(step != it)
  v.attachedNets.keepItIf(step != it)
  v.resize

  # UGLY:
proc uFullAngle(v: XVertex; s: Step): float =
  if s.next == nil or s.prev == nil:
    return NilFloat
  let v = s.vertex
  var d = arctan2(s.next.y - v.y, s.next.x - v.x) - arctan2(v.y - s.prev.y, v.x - s.prev.x)
  if d < -math.PI:
     d += math.TAU
  elif d > math.PI:
    d -= math.TAU
  return d

# UGLY: check and improve
proc sortAttachedNets(v: XVertex) = # by angle of total trace
  if v.attachedNets.len > 1:
    for n in items(v.attachedNets):
      assert(n.vertex == v)
      n.index = (uFullAngle(v, n) * 1000).int * (if n.rgt: 1 else: -1) # u for FullAngle(), CAUTION: int?
    #v.attachedNets.sortByIt(it.index)
    v.attachedNets.sort do (x, y: Step) -> int:
      result = cmp(x.index, y.index)
    for i, n in mpairs(v.attachedNets): n.index = i
    v.shash = initTable[(XVertex, XVertex), seq[Step]]()
    for n in mitems(v.attachedNets): # group attached nets with same angle (overlapping)
      let l = n.prev
      let r = n.next
      n.netDesc.flag = 1
      if v.shash.hasKey((l, r)):
        v.shash[(l, r)].add(n)
      elif v.shash.hasKey((r, l)):
        n.netDesc.flag = -1 # inverted direction
        v.shash[(r, l)].add(n)
      else:
        v.shash[(l, r)] = @[n]
    for group in v.shash.mvalues: # fine sort each group by following the traces
      if group.len > 1:
        group.reverse # for testing -- initialy reversing the group should give same result!
        for el in mitems(group):
          el.`ref` = el
        var indices = newSeq[int]()
        for el in group:
          indices.add(el.index)
        indices.sort
        var rel = newTable[(Step, Step), int]()
        for direction in [-1, 1]:
          var gr = group
          let final = true # for first direction we may get only a preliminary order?
          var unresolvedCombinations = false
          while gr.len > 1:
            #gr.map!{|el| (el.netDesc.flag == direction ? el.pstep : el.nstep)} # walk in one direction
            for el in gr:
              el.nstep.netDesc.flag = el.netDesc.flag
              el.pstep.netDesc.flag = el.netDesc.flag
            gr.applyIt(if it.netDesc.flag == direction: it.pstep else: it.nstep) # walk in one direction
            for el in gr:
              #assert el.nstep.ref != nil

              if el.netDesc.flag == direction:
                el.`ref` = el.nstep.`ref`
                assert el.ref != nil
              else:
                el.ref = el.pstep.ref
                echo el.netDesc.flag
                assert el.ref != nil
            #gr.each{|el| el.ref = (el.netDesc.flag == direction ? el.nstep.ref : el.pstep.ref)}
            for el in gr:
              el.score = uFullAngle(v, el)
            unresolvedCombinations = false
            for el in gr.combinations(2):
              let (a, b) = (el[0], el[1])
              let relation = rel.getOrDefault((a.ref, b.ref), NilInt)
              if relation == NilInt or relation.abs < 2:
                var c: int
                if a.score == NilFloat:
                  c = (if (b.rgt == b.ref.rgt): 1 else: -1)
                elif b.score == NilFloat:
                  echo a.ref != nil, "XXXXXXXXXXXXX"
                  c = (if (a.rgt == a.ref.rgt): -1 else: 1)
                else:
                  if (a.score * a.netDesc.flag.float - b.score * b.netDesc.flag.float).abs < 1e-6: # type of flag is int
                    c = 0
                  else:
                    c = -((a.score * (if a.ref.rgt: 1 else: -1)) <=> (b.score * (if b.ref.rgt: 1 else: -1)))
                if c != 0:
                  if final: # indicate final relation
                    c *= 2
                  rel[(a.ref, b.ref)] = c
                  rel[(b.ref, a.ref)] = -c
                else:
                  unresolvedCombinations = true
            if not unresolvedCombinations:
              break
            gr.keepItIf(it.next != nil and it.prev != nil)
          failif(unresolvedCombinations) # we should get at least a preliminary relation
          if final: break # indeed always -- we have no preliminary relations
        group.sort do (a, b: Step) -> int: # do we need rel[[a, b] <=> 0 to ensure -1,0,1 in block?
          result = rel[(a, b)]
        for el in group:
          el.index = indices.shift
    # attachedNets.sortByIt(-it.index)
    # attachedNets.sortBy!{|el| -el.index} # CAUTION: negative!
    v.attachedNets.sort do (a, b: Step) -> int:
          result = cmp(b.index, a.index)

proc newRegion(v: XVertex): Region =
  var r = Region()
  r.g = 1
  r.ox = 0
  r.oy = 0
  r.vertex = v
  r.rx = v.x
  r.ry = v.y
  r.neighbors = newSeq[Region]()
  r.incident = true
  r.outer = false
  return r

iterator qbors(r: Region; old: Region): (Region, bool, bool) =
  if old != nil:
    let ox = r.vertex.x
    let oy = r.vertex.y
    let ax = old.rx - ox
    let ay = old.ry - oy
    for el in r.neighbors:
      if el == old:
        continue
      var bx = el.rx - ox
      var by = el.ry - oy
      failif(old.vertex == el.vertex and r.idirs.len == 0)
      let turn = xbooleanReallySmartCrossProduct_2dWithOffset(old, el, r)
      bx = el.rx - ox
      by = el.ry - oy
      var inner = true
      var outer = r.incident
      if r.odirs.len > 0:
        outer = true
        for (zx, zy) in r.odirs:
          var j: bool
          if turn:
            j = ax * zy >= ay * zx and bx * zy <= by * zx # do we need = here?
          else:
            j = ax * zy <= ay * zx and bx * zy >= by * zx
          #break unless (outer &&= j)
          outer = outer and j
          if not outer: break
        inner = not outer
      for (zx, zy) in r.idirs:
        var j: bool
        if turn:
          j = ax * zy >= ay * zx and bx * zy <= by * zx # do we need = here?
        else:
          j = ax * zy <= ay * zx and bx * zy >= by * zx
        if j:
          inner = false
        else:
          outer = false
        if not (inner or outer):
          continue
      yield (el, inner, outer)
  else:
    for el in r.neighbors:
      yield (el, true, true)

proc distanceTo(r: Region; other: Region): float =
  hypot(r.vertex.x - other.vertex.x, r.vertex.y - other.vertex.y)

# note: the flow depends on the order of the traces -- trace with less clearance adjanced to trace with much clearance?
type
  Cut = ref object
    cap: float # vertex distance
    freeCap: float # cap - vertex copper - copper of passing traces
    cv1: float
    cv2: float # clearance of the two adjanced vertices
    cl: seq[float] # array of clearances for each trace passing -- order is important for overal space occupied

proc newCut(v1, v2: XVertex): Cut =
  var c = Cut()
  c.cap = hypot(v1.x - v2.x, v1.y - v2.y)
  c.freeCap = c.cap - v1.core - v2.core
  c.cv1 = Clearance # UGLY:
  c.cv2 = Clearance
  c.cl = newSeq[float]()
  return c

# return Maximum_Board_Diagonal (MBD) when there is no space available, or
# a measure for squeeze -- multiple of Average_Via_Size going to zero if there is much space available
proc squeezeStrength(c: Cut; traceWidth, traceClearance: float): float =
  var s: float
  if c.cl.len == 0:
    s = (if (c.cv1 < c.cv2 and c.cv1 < traceClearance): c.cv2 + traceClearance else: (if c.cv2 < traceClearance: c.cv1 + traceClearance else: c.cv1 + c.cv2))
  else:
    c.cl.add(traceClearance)
    #s2 = cl.permutation.map{|el| (el.unshift(@cv1).push(@cv2))}.map{|el| s = 0; el.eachCons(2){|a, b| s += [a, b].max}; s}.max
    # ss = cl.permutation.map{|el| el.unshift(@cv1).push(@cv2); s = 0; el.eachCons(2){|a, b| s += [a, b].max}; s}.max # slow
    # faster!
    let ll = c.cl.len div 2
    var hhh = c.cl.sorted#.reverse[0..ll] * 2
    hhh.reverse
    hhh = hhh[0..ll] & hhh[0..ll]
    if c.cl.len.isEven:
      discard hhh.pop
    hhh.add(c.cv1)
    hhh.add(c.cv2)
    hhh.sort
    #hhh.shift#(2)
    #hhh.shift
    hhh.delete(0)
    hhh.delete(0)
    #s = hhh.inject(0){|sum, v| sum + v}
    s = 0
    for el in hhh:
      s += el
    ### fail unless s == ss
    discard c.cl.pop
  s = c.freeCap - traceWidth - s
  if s < 0: MBD.float else: (10 * AVD * ATW).float / (ATW + s * 2).float

# we actually route that trace through this cut
proc use(c: Cut; traceWidth, traceClearance: float) =
  c.freeCap -= traceWidth
  c.cl.add(traceClearance)

# we put only one pin in each cell -- for testing
const
  CS = 3 * Pin_Radius

type
  Router = ref object
    filename: string
    b1x, b1y, b2x, b2y: float
    nameId: int
    path_ID: int
    image: cairo.Surface
    netlist: NetDescList
    pic: cairo.Context # debugging
    cell: Table[(int, int), int]
    cdtHash: Table[(int, int), XVertex]
    vertices: seq[XVertex]
    regions: seq[Region]
    #rstyles
    file: File # pcbLayoutDataFile
    edgesInCluster: Table[(XVertex, XVertex), int] # diagonal edge in pad/cluster, forbidden path, we may consider removing it from triagulation
    cdt: dt.DelaunayTriangulation
    newcuts: Table[(XVertex, XVertex), Cut]
    rand: random.Rand
    seed: int64

proc newRouter(b1x, b1y, b2x, b2y: float): Router =
  #XVertex.resetClass
  var r = Router()
  VertexClassID = 0
  VertexClusterID = 0
  (r.b1x, r.b1y, r.b2x, r.b2y) = (b1x, b1y, b2x, b2y) # corners of the PCB board
  #r.edgesInCluster = RouterSupport::HashWithOrderedArrayIndex.new
  r.nameId = 0
  r.path_ID = 0
  r.image = cairo.imageSurfaceCreate(Format.argb32, Board_Size, Board_Size)
  r.pic = newContext(r.image)
  r.pic.translate(40, 40)
  r.pic.scale(0.9, 0.9)
  let xExtent = (b2x - b1x).abs
  let yExtent = (b2y - b1y).abs
  let maxExtent = [xExtent, yExtent].max
  r.pic.scale(Board_Size / (maxExtent), Board_Size / (maxExtent))
  r.pic.translate(-b1x, -b1y)
  r.pic.translate((maxExtent - xExtent) / 2, (maxExtent - yExtent) / 2)
  r.pic.setSource(0.8, 0.8, 0.8, 1)
  r.pic.paint
  r.cdt = initDelaunayTriangulation(initVector(0, 0), initVector(PCBSize, PCBSize), vertexAllocProc = vertexAllocProc)
  for v in r.cdt.subdivision.vertices.values:
    XVertex(v).x = v.point.x
    XVertex(v).y = v.point.y
  #r.cdtHash = Hash.new
  #r.cell = H
  return r

#proc initSeed(r: Router; seed: int64 = 0) =
proc initSeed(r: Router) =
  var seed: int64
  if paramCount() == 1:
    seed = strutils.parseInt(paramStr(1))
  if seed == 0:
    let now = getTime()
    seed = now.toUnix * 1_000_000_000 + now.nanosecond
    seed = seed mod 100
    #r.rand = initRand(now.toUnix * 1_000_000_000 + now.nanosecond)
  #else:
  r.rand = initRand(seed)
  echo "Random seed: ", seed
  r.seed = seed

proc nextName(r: Router): string =
  r.nameId += 1
  return $r.nameId

# UGLY:
# insert some vertices on the boarder of the PCB board, should help
proc insertPcbBorder(r: Router) =
  var (a, b) = minmax(r.b1x, r.b2x)
  var d = (b - a) / (25)
  a -= d
  b += d
  let dx = (b - a) / (10)
  #(a..b).step(dx){|x|
  for x in countup(a, b, dx):
    var v = XVertex(x: x, y: r.b1y - d)
    v.name = "no"
    discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)
    v = XVertex(x: x, y: r.b2y + d)
    v.name = "no"
    discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)
    #r.cdt.insert(v)
  (a, b) = minmax(r.b1y, r.b2y)
  d = (b - a) / (25)
  a -= d
  b += d
  let dy = (b - a) / (10)
  a += dy
  b -= dy
  for y in countup(a, b, dy):
  #(a..b).step(dy){|y|
    var v = XVertex(x: r.b1x - d, y: y)
    v.name = "no"
    discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)
    #r.cdt.insert(v)
    v = XVertex(x: r.b2x + d, y: y)
    v.name = "no"
    discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)
    #r.cdt.insert(v)

#proc insertRescueVias(r: Router; l) =
#  #return
#  for x, y in l:
#  #l.each{|x, y|
#    insertPcbVertex("rescueVia", x, y, 1000, 1000)

# UGLY:
proc insertPcbVertex(r: Router; name: string; x, y, vt, vc: float) =
  if r.cdtHash.hasKey((x.int, y.int)):
    return
  #return if @cdtHash.include?([x, y]) # occurs for t.pcb
  var v = XVertex(x: x, y: y, vt: vt, vc: vc) # tracewidth and clearance?
  v.via = true
  v.name = name
  r.cdtHash[(x.int, y.int)] = v
  discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)

# Cluster from pcb
#[
proc insertCluster(r: Router; c: Cluster) =
  failif(c.convexPinHull.len == 0)
  let n = c.convexPinHull.size
  if n != 1:
    XVertex.beginNewCluster
  var lastVertex = nil
  var firstVertex = nil
  for cv in c.convexPinHull:
  #c.convexPinHull.each{|cv|
    let x = c.mx + cv.rx
    let y = c.my + cv.ry
    if r.cdtHash.include?([x, y]):
      fail
    else:
      v = XVertex.new(x, y, cv.thickness * 0.5, cv.clearance)
      v.name = c.name
      if n != 1:
        v.addToCurrentCluster
      if firstVertex == nil:
        firstVertex = v
      #firstVertex ||= v
      r.cdtHash[[x, y]] = v
      r.cdt.insert(v)
      r.cdt.insertConstraint(v, lastVertex) if lastVertex
      lastVertex = v
  r.cdt.insertConstraint(lastVertex, firstVertex) if n > 2

# UGLY: rename
proc testCluster(r: Router) =
  #r.cdt.edgesInConstrainedPolygons{|v1, v2|
  for v1, v2 in r.cdt.edgesInConstrainedPolygons:
    r.edgesInCluster[v1, v2] = true
]#

# UGLY:
proc generateTestVertices(r: Router) =
  # put a virtual pin on each corner of our board -- we should need this

#[
  for el in [0, PCB_Size] .tuples(2):
  # [0, PCB_Size].repeatedPermutation(2).each{|el|
    var v = XVertex(x: el[0], y: el[1])
    initialize(v, el[0], el[1])
    #r.cdt.insert(v)
    discard r.cdt.insertPoint(Vector(x: v.x.float, y: v.y.float), v)
    r.cell[(el[0] div CS, el[1] div CS)] = 1 # avoid collisions
]#

  var xid = 8
  while xid < Points:
    var (r1, r2) = (rand(r.rand, PCB_Size - PCB_Size div 50) + PCB_Size div 100, rand(r.rand, PCB_Size - PCB_Size div 50) + PCB_Size div 100)
    if not r.cell.hasKey((r1 div CS, r2 div CS)):# == nil:
      r.cell[(r1 div CS, r2 div CS)] = 1
      #if true#unless (300..500).include?(r1) or (300..500).include?(r2)
      var v = newXVertex(r1.float, r2.float) # x: r1, y: r2)
      discard r.cdt.insertPoint(Vector(x: v.x, y: v.y), v)
      #r.cdt.insert(v)
      xid += 1

proc generateNetlist(r: Router; l: seq[(int, int, int, int, string)]) =
  r.netlist = newSeq[NetDesc]()
  for el in l:
    var (x1, y1, x2, y2, style) = el
  #l.each{|x1, y1, x2, y2, style|
    var v1 = r.cdtHash[(x1, y1)]
    var v2 = r.cdtHash[(x2, y2)]
    assert( v1 != nil and v2 != nil)
    v1.numInets += 1
    v2.numInets += 1
    if v1.name.len == 0:
      v1.name = nextName(r)
    if v2.name.len == 0:
      v2.name = nextName(r)
    var netDesc = newNetDesc(v1.name, v2.name)
    netDesc.styleName = style
    netDesc.pri = (x2 - x1) ^ 2 + (y2 - y1) ^ 2
    r.netlist.add(netDesc)

proc sortNetlist(r: Router) =
  r.netlist.sort do (i, j: NetDesc) -> int:
    result = cmp(i.pri, j.pri)
    # r.netlist.sortBy!{|el| el.pri}

type
  XT = seq[XVertex]

proc finishInit(r: Router; rndTest = false) =
  r.vertices = newSeq[XVertex]()#Array.new # maybe later we do not need this array, we have @cdt.each{}
  r.regions = newSeq[Region](60)#Array.new
  #for v in r.cdt
  #r.cdt.each{|v|
  #echo r.cdt.subdivision.vertices
  for v in r.cdt.subdivision.vertices.values:
    #discard
    r.vertices.add(XVertex(v))
    var h = newRegion(XVertex(v))
    #r.regions.add(Region(vertex: XVertex(v)))
    #r.regions.add(h)
    r.regions[XVertex(v).xid] = h

  if rndTest:
    #var set = r.vertices.select{|el| el.xid > 3}.eachSlice(2).toA #.shuffle
    var set = toSeq(r.vertices.filterIt(it.xid.int > 3).chunked(2))
    set.sort do (i, j: XT) -> int:
      result = cmp((i[0].x - i[1].x) ^ 2 + (i[0].y - i[1].y) ^ 2, (j[0].x - j[1].x) ^ 2 + (j[0].y - j[1].y) ^ 2)
    #set.sortBy!{|el| (el[0].x - el[1].x) ^ 2 + (el[0].y - el[1].y) ^ 2}
    r.netlist = newSeq[NetDesc]()#NetDescList.new
    for i in 0 .. 9:
      var (v1, v2) = (set[i * 2][0], set[i * 2][1])
      if v1 != nil and v2 != nil:
        v1.name = $i & 's'
        v2.name = $i & 'e'
        var netDesc = NetDesc(t1Name:v1.name, t2Name: v2.name)
        r.netlist.add(netDesc)
  #r.newcuts = RouterSupport::HashWithOrderedArrayIndex.new
  for v in r.cdt.subdivision.vertices.values:
  #@cdt.each{|v|
    #for n in [v]:#r.cdt.neighborVertices(v): # NOTE: need fix
    #r.cdt.neighborVertices(v).each{|n|

    for n in v.neightbors:
      assert n != v
      XVertex(v).neighbors.add(XVertex(n))
      #if true:#r.regions[v.xid] != nil:
      if r.regions.len > XVertex(v).xid:
        assert n != v # r.regions[XVertex(v).xid].neighbors != r.regions[XVertex(n).xid]
        r.regions[XVertex(v).xid].neighbors.add(r.regions[XVertex(n).xid])
        for el in r.regions[XVertex(n).xid].neighbors:
          assert el != r.regions[XVertex(n).xid]
      var hx = newCut(XVertex(v), XVertex(n))
      r.newcuts[(XVertex(v), XVertex(n))] = hx#Cut.new(v, n)
      r.newcuts[(XVertex(n), XVertex(v))] = hx#Cut.new(v, n)
      assert(XVertex(v).core == XVertex(v).radius)

# UGLY: for debugging only
proc flagVertices(r: Router) =
  r.pic.setFontSize(2 * Pin_Radius)
  r.pic.setSource(1, 0, 0, 1)
  r.pic.setLineWidth(1)
  for v in r.vertices:
    r.pic.moveTo(v.x, v.y)
    r.pic.showText($v.xid)
    if v.visFlag != 0:
      if v.visFlag == 1:
        r.pic.setSource(1, 1, 1, 1)
      else:
        r.pic.setSource(0, 1, 0, 1)
      r.pic.newSubPath
      r.pic.setLineWidth(1)
      r.pic.arc(v.x, v.y, 0.3 * Pin_Radius, 0, 2 * math.PI)
      r.pic.fill
      r.pic.stroke

# UGLY:
proc drawVertices(r: Router) =
  r.pic.setSource(0, 0, 0, 0.3)
  r.pic.setLineWidth(100)
  for v in r.vertices:
    r.pic.newSubPath
    if v.cid == -1:
      r.pic.arc(v.x, v.y, v.core, 0, 2 * math.PI)
    else:
      r.pic.arc(v.x, v.y, Pin_Radius, 0, 2 * math.PI)
    r.pic.fill
    r.pic.stroke
    for n in v.neighbors:
      if r.edgesInCluster.hasKey((v, n)):
        r.pic.setSource(1, 0, 0, 0.3)
        r.pic.moveTo(v.x, v.y)
        r.pic.lineTo(n.x, n.y)
        r.pic.stroke
      else:
        r.pic.setSource(0, 0, 0, 0.3)
        r.pic.moveTo(v.x, v.y)
        r.pic.lineTo(n.x, n.y)
        r.pic.stroke
  r.pic.stroke
  r.pic.setSource(1, 0, 0, 0.7)
  r.pic.setLineWidth(600)
  for k, v in r.newcuts:
    if false:#k[0][].addr < k[1][].addr:
      r.pic.moveTo(k[0].x, k[0].y)
      r.pic.lineTo(k[1].x, k[1].y)
  #unless v.cid >= 0 && v.cid == k.cid
    #if false:#v.cap < MinCutSize:
      #discard
      #@pic.moveTo(k[0].x, k[0].y)
      #@pic.lineTo(k[1].x, k[1].y)
  #end
  r.pic.stroke

proc genVias(r: Router) =
  for v in r.vertices:
    if v.via:
      r.file.write("Via[#{v.x.round} #{v.y.round} #{(2 * v.core).round} #{Clearance.round} #{0} #{1000} \"\" \"\"]\n")

proc genLine(r: Router; x0, y0, x1, y1, w: float) =
  r.pic.setLineWidth(w)
  r.pic.moveTo(x0, y0)
  r.pic.lineTo(x1, y1)
  r.pic.stroke
  r.file.write("Line[#{x0.round} #{y0.round} #{x1.round} #{y1.round} #{w.round} #{Clearance.round} \"\"]\n")

# from, to should be in the range -PI..PI (from atan2()) or maybe 0..2PI?
proc genArc(r: Router; x, y: float; ra, frm, to, width: float) =
  var to = to
  r.pic.newSubPath
  r.pic.setLineWidth(width)
  r.pic.arc(x, y, ra, frm, to)
  r.pic.stroke
  if to < frm: # cairo does this internally, so PCB program need this fix
      to += 2 * math.PI
  let pcbStartAngle = ((math.PI - frm) * 180 / math.PI).round
  let pcbDeltaAngle = ((frm - to) * 180 / math.PI).round # never positive -- maybe we should flip angles?
  if pcbDeltaAngle != 0:
    r.file.write("Arc[#{x.round} #{y.round} #{r.round} #{r.round} #{width.round} #{Clearance.round} #{pcbStartAngle} #{pcbDeltaAngle} \"\"]\n")

# http://www.faqs.org/faqs/graphics/algorithms-faq/
# http://www.ecse.rpi.edu/Homepages/wrf/Research/Short_Notes/pnpoly.html
# int pnpoly(int nvert, float *vertx, float *verty, float testx, float testy)
# {
#   int i, j, c = 0;
#   for (i = 0, j = nvert-1; i < nvert; j = i++) {
#     if ( ((verty[i]>testy) != (verty[j]>testy)) &&
#    (testx < (vertx[j]-vertx[i]) * (testy-verty[i]) / (verty[j]-verty[i]) + vertx[i]) )
#        c = !c;
#   }
#   return c;
# }
#
# input: array of vertices
# result: the vertices inside the polygon (or on the border?)
proc verticesInPolygon(pVertices, testVertices: openArray[XVertex]): seq[XVertex] =
  #for el in testVertices:
  #  assert el.x != NaN and el.y != NaN
  #for el in pVertices:
  #  assert el.x != NaN and el.y != NaN
  var res: seq[XVertex]
  let nm1 = pVertices.len - 1
  for tp in testVertices:
    let ty = tp.y
    var i = 0
    var j = nm1
    var c = false
    while i <= nm1:
      if ((((pVertices[i].y <= ty) and (ty < pVertices[j].y)) or
           ((pVertices[j].y <= ty) and (ty < pVertices[i].y))) and
          (tp.x < (pVertices[j].x - pVertices[i].x) * (ty - pVertices[i].y) / (pVertices[j].y - pVertices[i].y) + pVertices[i].x)):
         c = not c
      j = i
      i += 1
    if c:
      res.add(tp)
  return res

#     (x2,y2)
#    /
#   /    (x0,y0)
#  /
# (x1,y1)
# http://mathworld.wolfram.com/Point-LineDistance2-Dimensional.html
proc distanceLinePoint(x1, y1, x2, y2, x0, y0: float): float =
  let x12 = x2 - x1
  let y12 = y2 - y1
  (x12 * (y1 - y0) - (x1 - x0) * y12).abs / hypot(x12, y12).float

proc distanceLinePointSquared(x1, y1, x2, y2, x0, y0: float): float =
  let x12 = x2 - x1
  let y12 = y2 - y1
  (x12 * (y1 - y0) - (x1 - x0) * y12) ^ 2 / (x12 ^ 2 + y12 ^ 2)

  #      (c)
  #     /
  #    /     (p)
  #   /
  # (b)
  # see http://www.geometrictools.com/
  # see also http://paulbourke.net/geometry/pointlineplane/
  #
proc unusedDistanceLineSegmentPointSquared(bx, by, cx, cy, px, py: float): float =
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

proc normalDistanceLineSegmentPointSquared(bx, by, cx, cy, px, py: float): float =
  let mx = cx - bx
  let my = cy - by
  let hx = px - bx
  let hy = py - by
  let t0 = (mx * hx + my * hy) / (mx ^ 2 + my ^ 2)
  if t0 > 0 and t0 < 1:
    (hx - t0 * mx) ^ 2 + (hy - t0 * my) ^ 2
  else:
    Maximum_Board_Diagonal.float

# Intersection point of two lines in 2 dimensions
# http://paulbourke.net/geometry/pointlineplane/
proc lineLineIntersection(x1, y1, x2, y2, x3, y3, x4, y4: float): array[4, float] =
  let x2x1 = x2 - x1
  let y2y1 = y2 - y1
  let d = (y4 - y3) * x2x1 - (x4 - x3) * y2y1
  if d == 0: # parallel?
    return [NilFloat, NilFloat, NilFloat, NilFloat]
  let ua = ((x4 - x3) * (y1 - y3) - (y4 - y3) * (x1 - x3)) / d
  let ub = (x2x1 * (y1 - y3) - y2y1 * (x1 - x3)) / d
  [x1 + ua * x2x1, y1 + ua * y2y1, ua, ub] # ub not needed? check!

const
  P_IN = 1
  P_ON = 0
  P_OUT = -1
  COLLINEAR = -2
# see http://en.wikipedia.org/wiki/BarycentricCoordinates_%28mathematics%29
proc unusedPointInTriangle(x1, y1, x2, y2, x3, y3, x, y: float): int =
  let d = (y2 - y3) * (x1 - x3) + (x3 - x2) * (y1 - y3)
  if d == 0:
    return COLLINEAR # maybe check if x,y is ... -- currently we do not care
  let l1 = ((y2 - y3) * (x - x3) + (x3 - x2) * (y - y3)) / d
  let l2 = ((y3 - y1) * (x - x3) + (x1 - x3) * (y - y3)) / d
  let l3 = 1 - l1 - l2
  let (min, max) = ([l1, l2, l3].min, [l1, l2, l3].max)
  if 0 <= min and max <= 1:
    if 0 < min and max < 1: P_IN else: P_ON
  else:
    P_OUT

proc unusedVerticesInTriangle(x1, y1, x2, y2, x3, y3: float; vertices: seq[XVertex]): seq[XVertex] =
  let d = (y2 - y3) * (x1 - x3) + (x3 - x2) * (y1 - y3)
  var vIn: seq[XVertex]
  if d == 0:
    echo "verticesInTriangle, degenerated"
    return vIn
  let y2my3 = (y2 - y3) / d
  let x3mx2 = (x3 - x2) / d
  let x1mx3 = (x1 - x3) / d
  let y3my1 = (y3 - y1) / d
  for v in vertices:
    let vxmx3 = v.x - x3
    let vymy3 = v.y - y3
    let l1 = y2my3 * vxmx3 + x3mx2 * vymy3
    let l2 = y3my1 * vxmx3 + x1mx3 * vymy3
    let (min, max) = ([l1, l2, 1 - l1 - l2].min, [l1, l2, 1 - l1 - l2].max)
    if 0 <= min and max <= 1:
      vIn.add(v)
  vIn

# see http://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/ConvexHull/MonotoneChain
proc unusedHcross(o, a, b: (float, float)): float =
  (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

#proc unusedConvexHull(points: seq[(int, int)]): seq[(int, int)] =
type
  HX = (float, float)

proc unusedConvexHull(points: var seq[HX]): seq[HX] =
  points.sort do (a, b: HX) -> int:
    result = cmp(a[0], b[0])
    if result == 0:
      result = cmp(a[1], b[1])
  points = deduplicate(points, isSorted = true)
  #points.sort#!.uniq!
  if points.len < 3:
    return points
  var lower = newSeq[HX]()
  for p in points:
    while lower.len > 1 and unusedHcross(lower[^2], lower[^1], p) <= 0:
      discard lower.pop
    lower.add(p)
  var upper = newSeq[HX]()
  #points.reverseEach{|p|
  #for p in points.reverse:
  reverse(points)
  for p in (points):
    while upper.len > 1 and unusedHcross(upper[^2], upper[^1], p) <= 0:
      discard upper.pop
    upper.add(p)
  return lower[0..^2] & upper[0..^2]

# http://en.wikipedia.org/wiki/TangentLinesToCircles
# http://www.ambrsoft.com/TrigoCalc/Circles2/Circles2Tangent_.htm
# https://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/TangentsBetweenTwoCircles
# UGLY: what when tangent does not exist?
proc getTangents(x1, y1, r1: float; l1: bool; x2, y2, r2: float; l2: bool): (float, float, float, float) =
  failif r1 < 0 or r2 < 0
  let d = math.hypot(x1 - x2, y1 - y2)
  let vx = (x2 - x1) / d
  let vy = (y2 - y1) / d
  var r2 = r2 * (if l1 == l2: 1 else: -1)
  let c = (r1 - r2) / d
  var h = 1 - c ^ 2
  if h < 0:
    discard
  if h >= 0:
    #h = 0 if h < 0 # wrong -- only for inspection
    h = math.sqrt(h) * (if l1 == true: -1 else: 1)
  else:
    h = 0
  let nx = vx * c - h * vy
  let ny = vy * c + h * vx
  (x1 + r1 * nx, y1 + r1 * ny, x2 + r2 * nx, y2 + r2 * ny)

proc newConvexVertices(vertices: var seq[XVertex]; prev, nxt, hv1, hv2: XVertex): seq[XVertex] =
  #failif(vertices.contains(prev) or vertices.contains(nxt))
  if vertices.len == 0:
    return vertices
  var (x1, y1, x2, y2) = getTangents(prev.x, prev.y, prev.tradius, prev.trgt, nxt.x, nxt.y, nxt.tradius, nxt.trgt)
  let v1 = XVertex(x: x1, y: y1, tradius: 100, xid: 999)
  let v2 = XVertex(x: x2, y: y2, tradius: 100, xid: 998)
  #vertices << v1 << v2 << hv1 << hv2
  vertices.add([v1, v2, hv1, hv2])
  var qhd: QuickhullDisk
  var s, res: ListCircularDisk2D
  #vertices.each{|v| ag.insert(v, v.x, v.y, v.tradius)}
  for v in vertices:
    s.add(initCircularDisk2D(v.x, v.y, v.tradius + 10, v.xid))
  if vertices.len > 0:
    echo vertices
    findHullDisks(qhd, s, res)
    if res.len > 1:
      assert res[0] == res[^1]
      res.setLen(res.high)
  var h: seq[int]
  for el in res:
    h.add(el.get_ID)
  vertices.keepItIf(it.xid in h)
  x2 -= x1
  y2 -= y1
  vertices -= [v1, v2, hv1, hv2]
  result = vertices.sortedByIt((it.x - x1) * x2 + (it.y - y1) * y2)
  #(ag.convexHullArray - [v1, v2, hv1, hv2]).sortBy{|el| (el.x - x1) * x2 + (el.y - y1) * y2}

const
  RRbNil = (nil, nil, false)

proc `<`(a, b: (Region, Region, bool, float)): bool =
  return a[3] < b[3]

#     a
#    /
#   /   select these neighbors of n
#  /    in inner angle < PI
# n______B
proc newBorList(a, b, n: Region): seq[XVertex] =
  let (aa, bb, nn) = (a, b, n)
  let (a, b, n) = (a.vertex, b.vertex, n.vertex)
  let ax = a.x - n.x
  let ay = a.y - n.y
  let bx = b.x - n.x
  let by = b.y - n.y
  n.neighbors.filter do (el: XVertex) -> bool:
    if el == a or el == b:
      false
    else:
      let ex = el.x - n.x
      let ey = el.y - n.y
      if xbooleanReallySmartCrossProduct_2dWithOffset(aa, bb, nn):
        ax * ey > ay * ex and ex * by > ey * bx
      else:
        ax * ey < ay * ex and ex * by < ey * bx

proc dijkstraUsePath(r: Router; path: seq[Region]; netDesc: NetDesc) =
  for uvw in path.windowed(3): # inverted direction, but it ...
    var (u, v, w) = (uvw[0], uvw[1], uvw[2])
    var lcuts: seq[XVertex]
    if u.vertex == w.vertex: # the 2 PI turn already seen above
      discard#lcuts = Array.new
    else:
      lcuts = newBorList(u, w, v) # neighbours in the inner angle/lane
      # fail unless lcuts == newBorList(w, u, v) # ... does not matter
    if v.outer:
      lcuts = v.vertex.neighbors - (lcuts & @[u.vertex, w.vertex])
    for el in lcuts:
      use(r.newcuts[(v.vertex, el)], netDesc.traceWidth, netDesc.traceClearance)
    #lcuts.each{|el| @newcuts[v.vertex, el].use(netDesc.traceWidth, netDesc.traceClearance)}
    if (u != path[0]) and ((u.outer == u.lrTurn) != (v.outer == v.lrTurn)):
      r.newcuts[(u.vertex, v.vertex)].use(netDesc.traceWidth, netDesc.traceClearance)
  path[0].outer = false
  path[0].lrTurn = false
  path[^1].outer = false
  path[^1].lrTurn = false

# https://en.wikipedia.org/wiki/Dijkstra%27sAlgorithm
# u --> v --> w
# Dijkstra's shortest path search -- along the edges of the constrained delaunay triangulation
#
#        v-----w
#  \    / \
#   \  /   \ lcut
#    u      x
#
# Generally we route at the inner lane -- doing so ensures that traces never cross.
# When the turn at u is opposite to the turn at v then we have to cross
# the line segment connecting u and v -- we need space for that.
# When we take the inner lane at v, then the lcut to vertex x is a restriction.
# When there starts an incident net in the inner lane this path
# is blocked, so we can use the outer lane, there can exist no inner
# crossing lanes. If we take the outer lane at v and inner lane at u,
# we have not to cross the line segment connection u and v and so on...
#
# So for this variant of Dijkstra's shortest path search we have not only to
# record the previous node, but also the lane (inner/outer) we took, because
# the next node may be only reachable when we do not have to cross a line
# segment between current and next node. We also record the parent of the previous
# node (u) -- because we have to check if there exists a terminal too close to u-v.
#
# So the key for the Fibonacci_Queue and parents and distances is not simple
# a node, but a tripel of node, previous node and lane.
#
# Update October 2015: Now we generally use outer lanes also -- for that qbors()
# function was changed. We still have to see if outer lanes really give benefit.
#
# Default unit of Size is 0.01 mil
# We will put this into a config file later

#  TODO: Check backside of first and last vertex of each path -- i.e. when traces
#  are thicker than pad or pin. Maybe we should leave that for manually fixing.
#  Ckecking is not really easy, and automatic fixing is some work.
#
#  (1.) Note: the cm arroach can fail for this case
#  (cm of neightbors of x is v, so distance to v is zero
#
#    /____    x  /____
#   /\        /\/
#   ||        || v
#
proc dijkstra(r: Router; startNode: Region; endNodeName: string; netDesc: NetDesc; maxDetourFactor:float = 2): seq[Region] =
  assert(startNode is Region)
  assert(endNodeName is string)
  assert(netDesc is NetDesc)
  failif(endNodeName.len == 0)
  failif(startNode.vertex.name == endNodeName)
  var q = initHeapQueue[(Region, Region, bool, float)]()
  var distances: Table[(Region, Region, bool), float]
  var parents: Table[(Region, Region, bool), (Region, Region, bool)]
  var outerLane: Table[(Region, Region, bool), bool] # record if we used inner or outer trail
  distances[(startNode, nil, true)] = 0 # fake left and right turn before start node
  distances[(startNode, nil, false)] = 0
  var (x, y) = startNode.vertex.xy
  var startCid = startNode.vertex.cid # cluster xid, -1 means no pad/cluster but plain pin
  for w, useInner, useOuter in startNode.qbors(nil): # initial steps are never blocked, so fill them in
    let u = (w, startNode, false) # for rgt == true and rgt == false, so we can continue in all directions
    let v = (w, startNode, true)
    let newpri: float = (if (startCid != -1) and (w.vertex.cid == startCid): 0.0 else: hypot(w.vertex.x - x, w.vertex.y - y))
    q.push((w, startNode, false, newpri))
    q.push((w, startNode, true, newpri))
    distances[(w, startNode, false)] = newpri
    distances[(w, startNode, true)] = newpri
    parents[u] = (startNode, nil, false) # arbitrary u and rgt for last two array elements
    parents[v] = parents[u]
  var min: (Region, Region, bool)
  var oldDistance: float
  while true:
    if q.len == 0:
      return #nil
    let minOldDistance = q.pop # what when empty?
    let (v, uu, prevRgt, oldDistance) = minOldDistance
    min = (v, uu, prevRgt)
    assert(v != nil and uu != nil)
    if distances.hasKey(min) and distances[min] < minOldDistance[3]:
      echo "continue"
      continue
    let hhh = (if (uu == startNode) or (uu.vertex.cid == startCid and startCid != -1): 0.0 else: uu.vertex.radius + [uu.vertex.separation, netDesc.traceClearance].max + netDesc.traceWidth / 2)
    var pom = parents.getOrDefault(min, RRbNil) # parent of min
    var popom = parents.getOrDefault(pom, RRbNil)
    var popom0: Region
    var popomv: XVertex
    if popom != RRbNil:
      popom0 = popom[0]
    if popom0 != nil:
      popomv = popom0.vertex
    if (v.vertex.name == endNodeName) and v.incident: # reached destination -- check if we touched a vertex
      echo "reached destination ", minOldDistance[3]
      let hhht: (float, float, float, float) = getTangents(uu.vertex.x, uu.vertex.y, hhh, prevRgt, v.vertex.x, v.vertex.y, 0, false) # last two arguments are arbitrary
      var blocked = false
      for el in uu.vertex.neighbors & v.vertex.neighbors:
        if el.cid == -1 or (el.cid != uu.vertex.cid and el.cid != v.vertex.cid) and el != popomv: # is this useful here?
          if normalDistanceLineSegmentPointSquared(hhht[0], hhht[1], hhht[2], hhht[3], el.x, el.y) < (el.radius + [el.separation, netDesc.traceClearance].max + netDesc.traceWidth / 2) ^ 2:
            blocked = true
            break
      if blocked:
        continue
      # for now avoid long twisted paths which may block others
      if minOldDistance[3] > 10 * AVD and minOldDistance[3] > maxDetourFactor * hypot(v.vertex.x - startNode.vertex.x, v.vertex.y - startNode.vertex.y):
        echo "refused"
        return #nil
      break # useless here
    let vcid = v.vertex.cid
    distances[min] = minOldDistance[3]
    let (x, y) = v.vertex.xy
    pom = parents[min] # parent of min
    popom = parents.getOrDefault(pom, RRbNil)
    if popom != RRbNil:
      popom0 = popom[0]
    if popom0 != nil:
      popomv = popom0.vertex
    let u = pom[0]
    assert u == uu
    var path: HashSet[Region] # prevent loops
    var p = min
    while p != RRbNil:
      path.incl(p[0])
      p = parents.getOrDefault(p, RRbNil)
    var blockingVertex: XVertex = nil # NOTE: benefit of this relaxation has not been observed yet!
    # NOTE: this is a bit too restrictive: when we touch a vertex, this path is still valid if next step is exactly this vertex. Rare and difficult.
    var uvBlocked = [false, true]
    for b in [false, true]:
    #uvBlocked = [false, true].map{|b| # does path u-v touch a vertex if we use inner/outer lane at v? [curRgt==false, curRgt==true]
      #let b = it
      var blocked = false
      var p = getTangents(uu.vertex.x, uu.vertex.y, hhh, prevRgt, v.vertex.x, v.vertex.y, v.vertex.radius + [v.vertex.separation, netDesc.traceClearance].max + netDesc.traceWidth / 2, b)
      for el in (uu.vertex.neighbors & v.vertex.neighbors): # NOTE: There may also exist other vertices touching the path -- very rare case!
      #(uu.vertex.neighbors & v.vertex.neighbors).each{|el| # NOTE: There may also exist other vertices touching the path -- very rare case!
        if (el.cid == -1 or (el.cid != uu.vertex.cid and el.cid != v.vertex.cid)) and el != popomv:
          if normalDistanceLineSegmentPointSquared(p[0], p[1], p[2], p[3], el.x, el.y) < ((el.radius + [el.separation, netDesc.traceClearance].max + netDesc.traceWidth / 2)) ^ 2:
            failif normalDistanceLineSegmentPointSquared(p[0], p[1], p[2], p[3], el.x, el.y) != unusedDistanceLineSegmentPointSquared(p[0], p[1], p[2], p[3], el.x, el.y)
            blocked = true
            if blockingVertex != nil: # both block, so this path is really blocked, no relaxation possible
              blockingVertex = nil
            else:
              blockingVertex = el
            break # caution, this break from the ruby code looks strange!
      uvBlocked[b.ord] = blocked
    for w, useInner, useOuter in v.qbors(u):
      let onlyOuter = not useInner
      if r.edgesInCluster.hasKey((v.vertex, w.vertex)): # diagonal edge in pad/cluster
        continue
      var hhh = false
      if false: #u == w && u != startNode # direct connection of two adjanced vertices, allow 2 PI loop around
      # indeed this can currently not work: we store lrTurn and outer attributes in region for each step, but do not copy region!
        discard#for el in
        #v.vertex.incidentNets.map{|el| el.nstep || el.pstep}.each{|el|
        # hhh = true if !(el.nstep && el.pstep) && (el.vertex == u.vertex)
        #}
      else:
        if path.contains(w):
          continue
      var lcuts: seq[XVertex]
      var lrTurn: bool
      if false: # we ignore this for now -- complicated and not really necessary...
      #if hhh && pom[1] != v && pom[1] != w && pom[1].vertex != v.vertex && pom[1].vertex != w.vertex
        let onlyOuter = true
        lrTurn = xbooleanReallySmartCrossProduct_2dWithOffset(pom[1], w, v)
      elif false:#u.vertex == w.vertex # 2 PI turn -- determine left/right turn by center of mass of neightbors
        #fail unless onlyOuter
        discard
        #cm = [u.neighbors, w.neighbors].map{|el|
        # Tex.new(el.inject(0){|sum, n| sum + n.vertex.x}.fdiv(el.length), el.inject(0){|sum, n| sum + n.vertex.y}.fdiv(el.length))
        #}
        #next if cm.find{|el| el.x == v.vertex.x && el.y == v.vertex.y} # see note (1.) above
        #next if cm[0].x == cm[1].x && cm[0].y == cm[1].y # can this occur?
        #lrTurn = RBR::booleanReallySmartCrossProduct_2dWithOffset(cm[0], cm[1], v.vertex) # left or right turn?
        #lcuts = Array.new # we need an empty lcuts array for outer turn
      else:
        lrTurn = xbooleanReallySmartCrossProduct_2dWithOffset(u, w, v) # left or right turn?
      var curRgt = lrTurn
      let wVRgt = (w, v, curRgt)
      let wVXrgt = (w, v, not curRgt)
      # CAUTION: may be wrong -- leave start cluster and come back? But should be no problem, we occupy the cluster early.
      #if false:# (startCid != -1) and (vcid == startCid) and (w.vertex.cid == startCid): # free walk around boundary of start cluster
      #  for el in [wVRgt, wVXrgt]:
      #    if not distances.contains(el):
      #      if q.incOrPush((el[0], el[1], el[2], oldDistance), oldDistance):
      #        parents[el] = min
      #  continue

      # CAUTION: may be wrong -- leave start cluster and come back? But should be no problem, we occupy the cluster early.
      if (startCid != -1) and (vcid == startCid) and (w.vertex.cid == startCid): # free walk around boundary of start cluster
        assert false # during testing
        for el in [wVRgt, wVXrgt]:
          if not distances.hasKey(el) or distances[el] > oldDistance:
            q.push((el[0], el[1], el[2], oldDistance))
            outerLane[el] = false # we took the inner path
            parents[el] = min # record the path for backtracking
            distances[el] = oldDistance

      if onlyOuter and vcid > -1: # corner of cluster, inner path not allowed, outer also forbidden!
        continue
      var newDistance = minOldDistance[3] + hypot(w.vertex.x - x, w.vertex.y - y)
      let outerDistance = newDistance # save this value
      ### outerDistance = oldDistance + 1 * Math.hypot(w.vertex.x - x, w.vertex.y - y) # maybe some "scaling" ?
      var canOut = onlyOuter
      if not (onlyOuter) and not distances.contains(wVRgt):
        block blocked:
          # process test with <canOut = true> clauses first!
          var lcuts: seq[XVertex] = newBorList(u, w, v) # neighbours in the inner angle/lane
          if vcid >= 0: # at corner of pad/cluster
            if lcuts.anyIt(it.cid == vcid) or (u.vertex.cid == vcid and w.vertex.cid == vcid and lcuts.len == 0):
            #if lcuts.find{|el| el.cid == vcid} || (u.vertex.cid == vcid && w.vertex.cid == vcid && lcuts.empty?) # do we need && lcuts.empty? For concave cluster maybe?
              canOut = true
              break blocked
          # now test special case when we touch a terminal with incident nets
          #v.vertex.incidentNets.map{|el| el.nstep || el.pstep}.each{|el|
          for h in v.vertex.incidentNets:
            var el: Step
            if h.nstep != nil: el = h.nstep else: el = h.pstep
            let hhh = lcuts.contains(el.vertex)
            if hhh and (vcid == -1): # why && (vcid == -1) ?
              canOut = true
            if hhh: break blocked
            if not(el.nstep != nil and el.pstep != nil) and (curRgt != prevRgt) and (el.vertex == u.vertex): break blocked
          if uvBlocked[(if curRgt: 1 else: 0)] and blockingVertex != w.vertex: break blocked
          #squeeze = lcuts.inject(0){|sum, el| if (h = @newcuts[v.vertex, el].squeezeStrength(netDesc.traceWidth, netDesc.traceClearance)) >= MBD; break h end; sum + h}
          var sum = 0.0
          for el in lcuts: # caution: this can force use of outer late!
            var h = squeezeStrength(r.newcuts[(v.vertex, el)], netDesc.traceWidth, netDesc.traceClearance) / 88
            sum += h
            #if h > sum: sum = h
            if sum >= MBD: break

          var squeeze = sum * 1
          if squeeze >= MBD.float: break blocked
          if (u != startNode) and (curRgt != prevRgt):
            squeeze += r.newcuts[(v.vertex, u.vertex)].squeezeStrength(netDesc.traceWidth, netDesc.traceClearance) + 0 * AVD # if (u != startNode) && (curRgt != prevRgt)
            #squeeze = 0 * AVD
          if squeeze >= MBD: break blocked
          let hhh = r.newcuts.getOrDefault((w.vertex, u.vertex), nil) # looking for shorter paths
          if true:#hhh != nil:
            #let nd = (newDistance + distances[pom] + hhh.cap) / 2
            let nd = (hypot(w.vertex.x - u.vertex.x, w.vertex.y - u.vertex.y) + distances[pom] + 0 * newDistance) / 1

            if nd < newDistance:
              newDistance = [nd, minOldDistance[3]].max
          else:
            if lcuts.len > 0: # can (only) occur for outer vertices of PCB rectangle
              #let nv = lcuts.minBy{|el| r.newcuts[v.vertex, el].cap}
              let nv = lcuts.minValueByIt(r.newcuts[(v.vertex, it)].cap)
              var nd: float
              if unusedPointInTriangle(u.vertex.x, u.vertex.y, v.vertex.x, v.vertex.y, w.vertex.x, w.vertex.y, nv.x, nv.y) >= 0: # P_IN = 1; P_ON = 0; P_OUT = -1; COLLINEAR = -2
                nd = hypot(u.vertex.x - nv.x, u.vertex.y - nv.y) + hypot(w.vertex.x - nv.x, w.vertex.y - nv.y)
              else:
                nd = hypot(u.vertex.x - w.vertex.x, u.vertex.y - w.vertex.y)
              nd = (newDistance + distances[pom] + nd) / 2
              if nd < newDistance:
                newDistance = [nd, minOldDistance[3]].max
          if false: # outerLane.hasKey((v, u, prevRgt)) and (curRgt != (prevRgt xor outerLane[(v, u, prevRgt)])): # wiggly line
            newDistance += AVD # this does not really improve the routing in all situations, so better disable it.
          newDistance += squeeze
          if not distances.hasKey(wVRgt) or distances[wVRgt] > newDistance:
            q.push((wVRgt[0], wVRgt[1], wVRgt[2], newDistance))
            outerLane[wVRgt] = false # we took the inner path
            parents[wVRgt] = min # record the path for backtracking
            distances[wVRgt] = newDistance
      if useOuter and not distances.contains(wVXrgt): # try outer path
        curRgt = not curRgt
        newDistance = outerDistance
        block blocked:
        #notBlocked = catch(:blocked){
          # lcuts = v.vertex.neighbors - (lcuts || newBorList(u, w, v)) - [u.vertex, w.vertex]
          if lcuts.len == 0:
            lcuts = newBorList(u, w, v)
          lcuts = v.vertex.neighbors - (lcuts & @[u.vertex, w.vertex]) # ugly!
#[
          var xxx: seq[XVertex]
          if lcuts.len != 0:
            xxx = lcuts
          else:
            discard#xxx = newBorList(u, w, v)
          xxx &= [u.vertex, w.vertex]
          lcuts.setLen(0)
          for el in v.vertex.neighbors: # also ugly :-)
            if el notin xxx:
              lcuts.add(el)
]#
          #squeeze = lcuts.inject(0){|sum, el| if (h = @newcuts[v.vertex, el].squeezeStrength(netDesc.traceWidth, netDesc.traceClearance)) >= MBD; break h end; sum + h}
          var sum = 0.0
          for el in lcuts:
            var h = squeezeStrength(r.newcuts[(v.vertex, el)], netDesc.traceWidth, netDesc.traceClearance) / 1
            sum += h
            if sum >= MBD: break
          var squeeze = sum
          if squeeze >= MBD: break blocked
          if (u != startNode) and (curRgt != prevRgt):
            squeeze += r.newcuts[(v.vertex, u.vertex)].squeezeStrength(netDesc.traceWidth, netDesc.traceClearance) + 4 * AVD# if (u != startNode) && (curRgt != prevRgt)
            #squeeze = 4 * AVD
          if squeeze >= MBD: break blocked
          if uvBlocked[(if curRgt: 1 else: 0)] and blockingVertex != w.vertex:
            break blocked
          # now test special case when we touch a terminal with incident nets
          #v.vertex.incidentNets.map{|el| el.nstep || el.pstep}.each{|el|
          for h in v.vertex.incidentNets:
            var el: Step
            if h.nstep != nil: el = h.nstep else: el = h.pstep
            if lcuts.contains(el.vertex):
              break blocked
            if not (el.nstep != nil and el.pstep != nil) and (curRgt != prevRgt) and (el.vertex == u.vertex):
              break blocked
          if false:#curRgt != prevRgt:#
            newDistance += AVD# if curRgt != prevRgt # TODO fix vertex size
          newDistance += squeeze
          if not distances.hasKey(wVXRgt) or distances[wVXRgt] > newDistance:
            q.push((wVXRgt[0], wVXRgt[1], wVXRgt[2], newDistance))
            outerLane[wVXRgt] = true # we took the outer path
            parents[wVXRgt] = min # record the path for backtracking
            distances[wVXRgt] = newDistance

  var path: seq[Region]
  var p = min
  while p != (nil, nil, false):
    var n = parents.getOrDefault(p, RRbNil)
    if n != (nil, nil, false):
      assert n[0] == p[1]
      #n[0].outer = outerLane[p]
      n[0].outer = outerLane.getOrDefault(p, false)
      #n[0].lrTurn = p[2] == outerLane[p]
      n[0].lrTurn = p[2] == n[0].outer
    path.add(p[0])
    p = n
  var cid = path[^1].vertex.cid
  if cid != -1: # ignore steps along edges of start cluster
    while path[-2].vertex.cid == cid:
      discard path.pop
  r.dijkstraUsePath(path, netDesc)
  return path

#          /neighbor
#     a   /
# <-------\
#       /  \b
#      /    \
#return neighbors of one side of the path
proc fullSplitNeighborList(a: Region; b: Region; n: Region): (seq[Region], seq[Region]) =
  assert a is Region
  assert b is Region
  var l: seq[Region]
  var r: seq[Region]
  let nx = n.vertex.x
  let ny = n.vertex.y
  let v1x = a.rx - nx
  let v1y = a.ry - ny
  let v2x = b.rx - nx
  let v2y = b.ry - ny
  var turn = xbooleanReallySmartCrossProduct_2dWithOffset(a, b, n)
  for el in n.neighbors:
    if el != a and el != b:
      let ex = el.rx - nx
      let ey = el.ry - ny
      if (if turn: v1x * ey > v1y * ex and v2x * ey < v2y * ex else: v1x * ey > v1y * ex or v2x * ey < v2y * ex):
        l.add(el)
      else:
        r.add(el)
  return (r, l)

proc atan2Tangents(a, b: XVertex; xid: int): float =
  let (lastStep, curStep) = (a.net(xid), b.net(xid))
  let t1 = getTangents(a.x, a.y, lastStep.radius, lastStep.rgt, b.x, b.y, curStep.radius, curStep.rgt)
  return math.arctan2(t1[3] - t1[1], t1[2] - t1[0])

# Explanation of the offset ox, oy used below
# -------------------------------------------
# We have a splitted region graph shown below,
# a result of a routed trace from X to Z.
# Region Y was splitted in regions y1 and y2.
#                         /B
#     /---------------- y1
# O--X------------------y2 \
#                       / \ \
#                       /   \ \
#                     A     Z
#
# One more trace along X--y1 will introduce one more region split
# along this path -- we split into neighbors to the left and to the right
# of the path. For neighbors A and B this is no problem, one is on the left,
# and one on the right of the path.
# Problem: The vertex of regions y1 and y2 is the same with identical cooordinates.
# When next trace is from O over X, y1 to B, y2 should be on the right side of
# the path. We add to each fresh split region a small delta offset perpendicular
# to the path, this allows a simple decision which is on the right or left side.
# This may not work when we have a 2 PI full turn -- currently in that case offset
# is zero. We may fix that if we use a more complicated offset calculation, but indeed
# for the full turn we do not need an offset. Indeed we need the offset only for the
# first and last splitted region of a path, not for inner regions. And a full turn
# should not occur for the first or last split.
#
# Splitting the path
# ------------------
# p, c, n -- previous, current, next region; c is splitted into r1 and r2
#
#  p       p        p
#  |      / \      / \
# -c-   -r1 r2-  -r1 r2-
#  |      \ /      |  |
#  n       n     -r1'r2'
#  |       |       \ /
#                   m
#
# template filterIt(s, pred: untyped): untyped
proc route(r: Router; netId: int; maxDetourFactor: float = 2): bool =
  failIf(netId > r.netlist.len - 1 or netId < 0)
  var netDesc = r.netlist[netId]
  let (frm, to) = (netDesc.t1Name, netDesc.t2Name)
  assert(frm.len != 0 and to.len != 0) # class is string or maybe integer?
  failif(frm == to)
  let startNodeList = r.regions.filterIt(it.incident and it.vertex.name == frm) # find intended!
  let startNode = startNodeList[0]
  assert startNode != nil
  #fail unless startNode = @regions.find{|r| r.incident && r.vertex.name == frm}
  if false:#r.rstyles != nil:
    discard#netDesc.traceClearance = @rstyles[netDesc.styleName].traceClearance
    discard#netDesc.traceWidth = @rstyles[netDesc.styleName].traceWidth
  else:
    netDesc.traceWidth = Trace_Width
    netDesc.traceClearance = Clearance
#[
=begin
very basic test for using rescue vias
  unless path = dijkstra(startNode, to, netDesc)
    netDesc = netDesc.dup
    netDesc.t2Name = 'rescueVia'
    path = dijkstra(startNode, 'rescueVia', netDesc)
    if path
      path[0].vertex.name = 'usedRescueVia'
    end
  end
  unless path #= dijkstra(startNode, to, netDesc)
=end
]#
  if maxDetourFactor == 0:
    return dijkstra(r, startNode, to, netDesc, 1.5).len != 0 # last arg was 1.5
  let path = dijkstra(r, startNode, to, netDesc, maxDetourFactor)
  if path.len == 0:
    if maxDetourFactor != 2:
      echo "dijkstra failed!"
      let xylist = r.regions.filterIt(it.incident and it.vertex.name == to) #find is intended!
      assert(xylist.len == 1)
      let (x, y) = (xylist[0].vertex.x, xylist[0].vertex.y)
      #(x, y) = r.regions.find{|r| r.incident && r.vertex.name == to}.vertex.xy
      r.pic.setSource(1, 1, 1, 1)
      r.pic.setLineWidth(ATW)
      r.pic.moveTo(x, y)
      r.pic.lineTo(startNode.vertex.x, startNode.vertex.y)
      r.pic.stroke
    return false
  let first = path[^1]
  let last = path[0]
  failif(first == last)
  if path.len > 2: # ignore direct connections without a single split region!
    first.idirs.add((path[^2].rx - first.vertex.x, path[^2].ry - first.vertex.y)) # same as above
    last.idirs.add((path[1].rx - last.vertex.x, path[1].ry - last.vertex.y))
    ###first.idirs << [cur.rx - first.rx, cur.ry - first.ry] # this may work when we fix qbors() too
  var r1, r2: Region
  r.pic.arc(first.vertex.x, first.vertex.y, 2 * ATW, 0, 6)
  r.pic.stroke
  r.pic.moveTo(first.vertex.x, first.vertex.y)
  r.pic.setFontSize(4 * Pin_Radius)
  r.pic.showText($netId)
  r.pic.stroke
  r.pic.moveTo(first.vertex.x, first.vertex.y)
  for prvcurnxt in path.reversed.windowed(3):
    let (prv, cur, nxt) = (prvcurnxt[0], prvcurnxt[1], prvcurnxt[2])
  #path.reverse.eachCons(3){|prv, cur, nxt|
    assert(prv != nil and cur != nil and nxt != nil)
    var (ne, neComp) = fullSplitNeighborList(prv, nxt, cur)
    failif(neComp.contains(prv) or neComp.contains(nxt))
    failif(ne.contains(prv) or ne.contains(nxt))
    ne.add(nxt)
    neComp.add(nxt)
    if r1 != nil:
      var i = ne.find(r2)
      if i >= 0:
        ne.delete(i)
      i = neComp.find(r1)
      if i >= 0:
        neComp.delete(i)
    else:
      ne.add(prv)
      neComp.add(prv)
    var iii = r.regions.find(cur)
    assert iii >= 0
    r.regions.delete(iii)
    r1 = newRegion(cur.vertex)
    r2 = newRegion(cur.vertex)
    r1.idirs = cur.idirs
    r2.idirs = cur.idirs
    r1.odirs = cur.odirs
    r2.odirs = cur.odirs
    r1.incident = cur.incident
    r2.incident = r1.incident
    # give r1 and r2 an offset vector perpendicular to the path to allow a distinction
    var (dx1, dy1, dx2, dy2) = (0.0, 0.0, 0.0, 0.0)
    if prv == first:
      dx2 = cur.rx - prv.rx
      dy2 = cur.ry - prv.ry
      let h = hypot(dx2, dy2)
      dx2 = dx2 / h
      dy2 = dy2 / h
    if nxt == last:
      dx1 = nxt.rx - cur.rx
      dy1 = nxt.ry - cur.ry
      let h = hypot(dx1, dy1)
      dx1 = dx1 / h
      dy1 = dy1 / h
    if prv == first or nxt == last:
      r1.g = cur.g / 2
      r2.g = r1.g
      var dy = (dx1 + dx2)
      var dx = -(dy1 + dy2)
      let h = hypot(dx, dy) / cur.g # zero for full 2 PI turn
      dx = dx / h
      dy = dy / h
      r1.ox = cur.ox + dx
      r1.oy = cur.oy + dy
      r2.ox = cur.ox - dx
      r2.oy = cur.oy - dy
      r1.rx = r1.vertex.x + r1.ox
      r1.ry = r1.vertex.y + r1.oy
      r2.rx = r2.vertex.x + r2.ox
      r2.ry = r2.vertex.y + r2.oy
    else:
      r1.ox = cur.ox
      r1.oy = cur.oy
      r2.ox = cur.ox
      r2.oy = cur.oy
      r1.rx = cur.rx
      r1.ry = cur.ry
      r2.rx = cur.rx
      r2.ry = cur.ry
    var dx, dy: float
    if true:#nxt.vertex != prv.vertex # h == 0
      dx1 = nxt.rx - cur.rx
      dy1 = nxt.ry - cur.ry
      var h = hypot(dx1, dy1)
      dx1 = dx1 / h
      dy1 = dy1 / h
      dx2 = cur.rx - prv.rx
      dy2 = cur.ry - prv.ry
      h = hypot(dx2, dy2)
      dx2 = dx2 / h
      dy2 = dy2 / h
      dy = (dx1 + dx2)
      dx = -(dy1 + dy2)
      h = hypot(dx, dy) #/ cur.g # zero for full 2 PI turn
      dx = dx / h
      dy = dy / h
    r.regions.add(r1)
    r.regions.add(r2)
    for el in cur.neighbors:
      let i = el.neighbors.find(cur)
      assert i >= 0
      el.neighbors.delete(i)
    for el in ne:
      el.neighbors.add(r1)
      r1.neighbors.add(el)
    for el in neComp:
      el.neighbors.add(r2)
      r2.neighbors.add(el)

    if cur.lrTurn != cur.outer:
      r1.incident = false
    else:
      r2.incident = false
    if cur.outer and dx != 0:
      if cur.lrTurn:
        r2.odirs.add((dx, dy))
      else:
        r1.odirs.add((-dx, -dy))
    r.pic.lineTo(cur.vertex.x, cur.vertex.y)
  r.pic.lineTo(last.vertex.x, last.vertex.y)
  r.pic.stroke
  var pstep: Step = nil
  for i, cur in pairs(path):
    let nxt = (if i == path.len - 1: nil else: path[i + 1])
    let prv = (if i == 0: nil else: path[i - 1])
    let nv = (if nxt != nil: nxt.vertex else: nil)
    let pv = (if prv != nil: prv.vertex else: nil)
    let cv = cur.vertex
    var step = newStep(pv, nv, r.path_ID)
    step.outer = cur.outer
    step.lrTurn = not cur.lrTurn
    step.netDesc = netDesc
    step.vertex = cv
    step.pstep = pstep
    pstep = step
    if prv != nil and nxt != nil:
      cv.update(step) # TODO: if one vertex includes his neighbor vertex, then skip that one!
      cv.unfriendlyResize
      step.rgt = step.outer != cur.lrTurn
      step.xt = not step.outer
      cv.attachedNets.add(step)
    else:
      step.rgt = false
      cv.incidentNets.add(step)
  r.path_ID += 1
  while true:
    let p = pstep.pstep
    if p == nil:
      break
    p.nstep = pstep
    pstep = p
  return true

proc smartReplace(step: Step; list: seq[XVertex]) =
  if step.prev == step.next: # can occur due to nubly()
    assert(list.len == 0) # should be empty?
    step.pstep.nstep = step.nstep.nstep
    step.pstep.next = step.nstep.next
    step.nstep.nstep.pstep = step.pstep
    step.nstep.nstep.prev = step.prev
    step.next.newDeleteNet(step.nstep)
  elif list.len == 0:
    let ps = step.pstep
    let ns = step.nstep
    ps.next = step.next
    ns.prev = step.prev
    ps.nstep = ns
    ns.pstep = ps
  else:
    var pstep = step.pstep
    var pv = step.prev
    for v in list:
      var n = newStep(pv, nil, step.xid)
      n.netDesc = step.netDesc
      n.vertex = v
      n.pstep = pstep
      pstep.nstep = n
      pstep.next = v
      pstep = n
      pv = v
      n.rgt = not step.rgt
      n.xt = true # TODO: check
      n.outer = true
      v.update(n)
      v.attachedNets.add(n)
    pstep.next = step.next
    pstep.nstep = step.nstep
    pstep.nstep.prev = pv
    pstep.nstep.pstep = pstep
  step.vertex.newDeleteNet(step)

  #\   |   /
  # \  |  /
  #  \ | /  3 attached concave nets not overlapping
  #    O ------------
  #     \ -----
  #      \
  #       \
  #        \
  # sort attached nets and calculate its radii.
  # this should work for concave (before attachment operator is applied) and convex final nets
  # regard groups by angle: overlapping angles needs different radii for arcs,
  # non overlapping attached arcs may have the same radius.
  # generally one terminal should have at least two final convex groups -- but a terminal with
  # a very big radius may have more than 2 attached groups.
  # Indeed nets never cross, so overlapping is full including
  # currently we collect all attached nets of a terminal in one single array called
  # attachedNets -- we may consider using a separate array for each group...
  # maybe we should regard minimal gap as overlapping? Introduce an eps?
  # UGLY: Unused
#
proc currentlyUnusedSmartPrepareSteps(r: Router) =
  for vert in r.vertices:
    if vert.attachedNets.len == 0:
      continue
    for s in vert.attachedNets:
      s.g = -1
      let a = atan2Tangents(s.vertex, s.next, s.xid) # -PI <= angle <= PI
      var b = atan2Tangents(s.prev, s.vertex, s.xid) # wrong direction, we have to flip
      if b < 0:
        b += math.PI
      else:
        b -= math.PI
      var d = (a - b).abs
      var dir = (a + b) / 2
      if d > math.PI: # select inner angle < PI -- and flip direction
        d = 2 * math.PI - d
        if dir < 0:
          dir += math.PI
        else:
          dir -= math.PI
      s.d = d / 2
      s.dir = dir
    var nets = vert.attachedNets.sortedByIt(it.dir)
    var i = nets.len
    var last = nets[0]
    last.dir += 2 * math.PI
    last.g = 0
    var group = 0
    while (i -= 1; i) > 0: # backward while in group 0, start with largest angle
      var nxt = nets[i]
      if nxt.dir + nxt.d < last.dir - last.d:
        break
      nxt.g = 0
      last = nxt
    i = 0
    last = nets[0]
    last.dir -= 2 * math.PI # undo above fix
    while (i += 1; i) < nets.len: # forward
      var nxt = nets[i]
      if nxt.g == 0:
        break
      if nxt.dir - nxt.d > last.dir + last.d:
        group += 1
      nxt.g = group
      last = nxt
    group = 0
    while true:
      vert.resetInitialSize
      var groupFound = false
      for step in vert.attachedNets:
        if step.g == group:
          groupFound = true
          var net = step.netDesc
          var traceSep = [vert.separation, net.traceClearance].max
          vert.radius += traceSep + net.traceWidth
          step.radius = vert.radius - net.traceWidth / 2
          vert.separation = net.traceClearance
      if not groupFound:
        break
      group += 1

# sort attached nets and calculate its radii
proc prepareSteps(r: Router) =
  for vert in r.vertices:
    if vert.attachedNets.len == 0:
      continue
    vert.resetInitialSize
    for b in [true, false]:
      for step in vert.attachedNets:
        if step.xt == b:
          continue
        let net = step.netDesc
        let traceSep = [vert.separation, net.traceClearance].max
        vert.radius += traceSep + net.traceWidth
        step.radius = vert.radius - net.traceWidth / 2
        vert.separation = net.traceClearance

proc sortAttachedNets(r: Router) =
  for vert in r.vertices:
    vert.sortAttachedNets
  #r.vertices.each{|vert| vert.sortAttachedNets}

proc ego(x: varargs[string, `$`]) =
  stdout.write(":::")
  for el in x:
    stdout.write(el, " ")
  echo ""

proc convexKkk(prevStep, step, nxtStep: Step): (float, float) =
  let (pv, cv, nv) = (step.prev, step.vertex, step.next)
  var (x1, y1, x2, y2) = getTangents(pv.x, pv.y, prevStep.radius, prevStep.rgt, cv.x, cv.y, step.radius, step.rgt)
  var (x3, y3, x4, y4) = getTangents(cv.x, cv.y, step.radius, step.rgt, nv.x, nv.y, nxtStep.radius, nxtStep.rgt)
  (x2, y2, x3, y3) = lineLineIntersection(x1, y1, x2, y2, x3, y3, x4, y4) # get crossing point and ua, ub
  if (x2 != NilFloat) and ((x3 > 0 and x3 < 1) or (y3 > 0 and y3 < 1)):
    return (x2, y2)
  else:
    return (NilFloat, NilFloat)

proc nubly(r: Router; collapse = false) =
  var replaced = true
  var repC = 0
  while replaced:
    replaced = false
    repC += 1
    for cv in r.vertices:
      for step in itemsReversed(cv.attachedNets):
        let (prevStep, nxtStep) = (step.pstep, step.nstep)
        let (pv, nv) = (step.prev, step.next)
        var d = (hypot(cv.x - pv.x, cv.y - pv.y) - (prevStep.radius - step.radius).abs * 1.02)
        if d < 0:
          if step.radius < prevStep.radius:
            step.radius -= d
            replaced = true
          continue
        d = (hypot(cv.x - nv.x, cv.y - nv.y) - (nxtStep.radius - step.radius).abs * 1.02)
        if d < 0:
          if step.radius < nxtStep.radius:
            step.radius -= d
            replaced = true
          continue
        var (hx, hy) = convexKkk(prevStep, step, nxtStep) # , r)
        step.xt = hx != NilFloat
        if collapse and step.xt:
          let (pv, nv) = (step.prev, step.next)
          let hv0 = newXVertex(hx, hy)
          replaced = true
          let pvx = pv.x
          let pvy = pv.y
          let nvx = nv.x
          let nvy = nv.y
          var pp = prevStep.pstep
          if pp != nil:
            (hx, hy) = convexKkk(pp, prevStep, step)
          var ppv: XVertex
          if pp != nil and hx != NilFloat:
            ppv = newXVertex(hx, hy)
          else:
            ppv = pv
          let nn = nxtStep.nstep
          if nn != nil:
            (hx, hy) = convexKkk(step, nxtStep, nn)
          var nnv: XVertex
          if nn != nil and hx != NilFloat:
            nnv = newXVertex(hx, hy)
          else:
            nnv = nv
          hx = nvx - pvx
          hy = nvy - pvy
          var vecX, vecY: float
          if step.rgt:
            (vecX, vecY) = (hy, -hx)
          else:
            (vecX, vecY) = (-hy, hx)
          let hv3 = newXVertex(pvx + hx / 2 + vecX, pvy + hy / 2 + vecY)
          hx *= 2
          hy *= 2
          vecX *= 2
          vecY *= 2
          let hv4 = newXVertex(pvx - hx + vecX, pvy - hy + vecY)
          let hv5 = newXVertex(nvx + hx + vecX, nvy + hy + vecY)
          var rep = verticesInPolygon([ppv, hv0, nnv, hv3], r.vertices) - [pv, nv, ppv, cv, nnv, hv3]
          if rep.len > 0:
            let net = step.netDesc
            for v in rep:
              v.trgt = not step.rgt
              v.tradius = v.radius + [net.traceClearance, v.separation].max + net.traceWidth / 2
            pv.trgt = step.pstep.rgt
            pv.tradius = step.pstep.radius
            nv.trgt = step.nstep.rgt
            nv.tradius = step.nstep.radius
            rep = newConvexVertices(rep, pv, nv, hv4, hv5)
          smartReplace(step, rep)

proc drawRoutes(r: Router; layer = 0) =

  discard r.file.open("layer_#{2 - layer}.pcb", fmwrite)
  r.file.write("FileVersion[20070407]\n")
  r.file.write("PCB[\"\" 350000 330000]\n")
  r.file.write("Grid[3900.0 1800 100 1]\n")
  if layer == 0:
    r.genVias()
    r.file.write("Layer(1 \"\")\n(\n")
  else:
   r.file.write("Layer(4 \"\")\n(\n")
  r.pic.setSource(0, 0, 0, 1)
  for vert in r.vertices:
    for n in vert.incidentNets:
      if n.next != nil:
        r.pic.newSubPath
        r.pic.arc(vert.x, vert.y, 100, 0, 2 * math.PI)
        r.pic.stroke
      let thi = n.netDesc.traceWidth
      let sep = n.netDesc.traceClearance
      var last = vert
      var lastx = 0.0#: XVertex = nil
      var lasty = 0.0#: XVertex = nil
      var lr = 0.0
      var to = n.next
      var toNet = n.nstep
      while to != nil:
        var t: (float, float, float, float)
        let lastNet = toNet.pstep
        last = lastNet.vertex
        let radius = toNet.radius
        if last.x == to.x and last.y == to.y:
          last.visFlag = 1
        else:
          t = getTangents(last.x, last.y, lr, lastNet.rgt, to.x, to.y, radius, toNet.rgt)
          r.genLine(t[0], t[1], t[2], t[3], thi)
          if lr > 0:
            var startAngle = math.arctan2(lasty - last.y, lastx - last.x)#.int
            var endAngle = math.arctan2(t[1] - last.y, t[0] - last.x)#.int
            if not lastNet.rgt:
              (startAngle, endAngle) = (endAngle, startAngle)# unless lastNet.rgt
            r.genArc(last.x, last.y, lr, startAngle, endAngle, thi)
            r.pic.setSource(0, 0, 0, 1)
        lr = radius
        last = to
        toNet = toNet.nstep
        if toNet != nil:
          to = toNet.vertex
        else:
          to = nil
        lastx = t[2]
        lasty = t[3]
  r.file.write(")\n")
  if r.file != nil:
    r.file.close

proc setLineWidth(r: Router; w: float) =
  r.pic.setLineWidth(w)

proc setColor(rr: Router; r, g, b, a: float) =
  rr.pic.setSource(r, g, b, a)

proc savePicture(r: Router) =
  discard r.image.writeToPng(r.filename)

proc main() =
  #let rs = initSeed()
  let r = newRouter(0, 0, PCB_Size, PCB_Size)#.new(0, 0, RBR::PCB_Size, RBR::PCB_Size)
  initSeed(r)
  r.generateTestVertices
  r.finishInit(true)
  r.filename = "pic" & ($r.seed) & ".png"
  r.drawVertices
  #col = ([1, 0, 0].permutation(3).toA + [1, 1, 0].permutation(3).toA).uniq - [[1, 0, 0]]

  var col = deduplicate(toSeq(combinatorics.permutations([1.0, 0, 0])) & toSeq(combinatorics.permutations([1.0, 1, 0])))
  r.setColor(1, 0, 0, 0.7)
  r.setLineWidth(1200)
  # [0,1,2,3,4,5,6,7,8,9].each{|i|
  for i in [6, 7, 8, 9]:#, 8, 9]: # [3, 4, 5, 6, 7]:#,1,2,3,4,5,6]:#,7,8,9]:
    r.setColor(col[i mod 5][0], col[i mod 5][1], col[i mod 5][2], 0.4)
    #discard r.route(strutils.parseInt(paramStr(1)))
    discard r.route(i)

  r.sortAttachedNets
  r.prepareSteps
  r.nubly
  r.prepareSteps
  r.sortAttachedNets
  r.prepareSteps
  r.nubly
  r.prepareSteps
  r.sortAttachedNets
  r.prepareSteps
  r.nubly(true)
  r.sortAttachedNets
  r.prepareSteps
  r.drawRoutes
  r.flagVertices
  r.savePicture

when isMainModule:
  main()
# 2275 lines float dup text proc popom find

#[
            for el in rep:
              if true: break
              r.pic.arc(el.x, el.y, 0.3* Pin_Radius, 0, 2*math.PI)
              if el.trgt:
                r.pic.setSource(1,0,0)
              else:
                r.pic.setSource(0,1,0)
              r.pic.fill
              r.pic.stroke

]#
