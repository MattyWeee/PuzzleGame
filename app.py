from cmu_graphics import *
import random, math, copy
import heapq

def almostEqual(x, y):
    return abs(x-y)<.0000001

def distance(x1, y1, x2, y2):
    return ((x1-x2)**2 + (y1-y2)**2)**0.5

def HeronsFormula(a, b, c):
    s = (a+b+c)/2
    return (s*(s-a)*(s-b)*(s-c))**0.5

def getDims(points):
    xVals_min, yVals_min, xVals_max, yVals_max = [], [], [], []
    for point in points:
        heapq.heappush(xVals_min, point.x)
        heapq.heappush(yVals_min, point.y)
        heapq.heappush(xVals_max, -1*point.x)
        heapq.heappush(yVals_max, -1*point.y)
    left, top = xVals_min[0], yVals_min[0]
    right, bottom = -1*xVals_max[0], -1*yVals_max[0]
    return left, top, right-left, bottom-top

def onSameLine(dir1, dir2):
    M = Matrix_2x2(dir1.vector, dir2.vector)
    return True if almostEqual(M.det, 0) else False

def parallel(dir1, dir2): 
    M = Matrix_2x2(dir1.vector, dir2.vector)
    if almostEqual(M.det, 0) and dir1.vector.dot(dir2.vector) > 0:
        return True
    return False

def moveToFront(elt, L): #moves elt to end of list
    L.remove(elt)
    L.append(elt)

def bounded(a, b, c):
    return (b < a or almostEqual(a, b)) and (a < c or almostEqual(a, c))

class Point():
    def __init__(self, x, y, angle=None):
        self.x = x
        self.y = y
        self.angle = angle #wrt some center to order in cw fashion
    
    def __repr__(self):
        return f'({self.x}, {self.y})'
    
    def __eq__(self, other):
        return isinstance(other, Point) and (self.x, self.y) == (other.x, other.y)
    
    def __hash__(self):
        return hash(str(self))
        
    def __lt__(self, other):
        return self.angle > other.angle 
    
    def unpack(self):
        return [self.x, self.y]
    
    def __add__(self, other):
        return Point(self.x+other.x, self.y+other.y)
    
    def __sub__(self, other):
        return Point(self.x-other.x, self.y-other.y)
    
    def moveTo(self, x, y):
        self.x = x
        self.y = y
    
    def distance(self, other):
        return distance(self.x, self.y, other.x, other.y)

    def onLine(self, line):
        temp = LineSegment(self, line.getEndPoint())
        if onSameLine(temp, line):
            minX, maxX = min(line.point1.x, line.point2.x), max(line.point1.x, line.point2.x)
            minY, maxY = min(line.point1.y, line.point2.y), max(line.point1.y, line.point2.y)
            return bounded(self.x, minX, maxX) and bounded(self.y, minY, maxY)
            
        return False

class Vector(Point): #in R3
    def __init__(self, x, y, z = 0):
        super().__init__(x, y)
        self.z = z
        self.magnitude = self.getMagnitude()
    
    def __repr__(self):
        return f'({self.x}i, {self.y}j, {self.z}k)'
    
    def __lt__(self, other):
        return self.magnitude < other.magnitude
        
    def scaled(self, factor):
        return Vector(self.x * factor, self.y * factor)
    
    def normalized(self):
        if self.magnitude == 0:
            return Vector(0, 0, 0)
        else:
            return Vector(self.x / self.magnitude, self.y / self.magnitude)
    
    def getMagnitude(self):
        return distance(self.x, self.y, 0, 0)
    
    def __add__(self, other):
        return Vector(self.x+other.x, self.y+other.y)
    
    def __sub__(self, other):
        return Vector(self.x-other.x, self.y-other.y)
    
    def moveTo(self, x, y):
        super().moveTo(x, y)
    
    def dot(self, other):
        return self.x*other.x + self.y*other.y + self.z*other.z
    
    def cross(self, other): #returns self cross other
        a, b, c, d, e, f = self.x, self.y, self.z, other.x, other.y, other.z
        i, j, k = b*f-c*e, c*d-a*f, a*e-b*d
        return Vector(i, j, k)
        
    def getOrthogonal(self): #returns an orthogonal vector that points "outward" in the sense that self is an edge of a polygon with edges pointing in cw direction
        k = Vector(0, 0, -1)
        return k.cross(self).normalized()
        
class Matrix_2x2():
    def __init__(self, vector1, vector2):
        self.a = vector1.x 
        self.b = vector2.x
        self.c = vector1.y
        self.d = vector2.y
        self.det = self.getDeterminant()
    
    def __repr__(self):
        return f'{[[self.a, self.b], [self.c, self.d]]}'
    
    def getDeterminant(self):
        a, b, c, d = self.a, self.b, self.c, self.d
        return a*d - b*c

class Ray():
    def __init__(self, point, vector):
        self.point1 = copy.deepcopy(point)
        self.vector = vector.normalized()
        
    def __repr__(self):
        return f'{self.point1}, {self.vector}'
    
    def hit(self, edge):
        vectorA, vectorB = self.vector, edge.vector
        pointA, pointB = self.point1, edge.point1
        M1 = Matrix_2x2(vectorA, vectorB)
        M2 = Matrix_2x2(vectorA, pointB - pointA)
        M3 = Matrix_2x2(vectorB, pointA - pointB)
        
        if almostEqual(M1.det, 0):
            if onSameLine(self, edge) and LineSegment(pointA, pointB).vector.dot(self.vector) > 0:
                scalarA1, scalarA2 = self.point1.distance(edge.point1), self.point1.distance(edge.point2)
                return (scalarA1, 0) if scalarA1 < scalarA2 else (scalarA2, 1)
            else:
                return None
        
        scalarA = M3.det / M1.det
        scalarB = M2.det / (-M1.det)
        
        if (almostEqual(scalarA, 0) or scalarA > 0) and (almostEqual(scalarB, 0) or almostEqual(scalarB, 1) or 0 < scalarB < 1): #endpoints count as intersection
            return (scalarA, scalarB)
        return None

class LineSegment():
    @staticmethod
    def getLinesFromPoints(points):
        n = len(points)
        return [LineSegment(points[i], points[(i+1)%n]) for i in range(n)] 
    
    def __init__(self, point1, point2):
        self.point1 = copy.deepcopy(point1)
        self.point2 = copy.deepcopy(point2)
        self.length = self.getLength()
        self.basis = self.getBasis()
        self.vector = self.basis.scaled(self.length)
        
        self.antennaRays = self.getAntennaRays()
        
    def __repr__(self):
        return f'{self.point1} to {self.point2}'
    
    def __eq__(self, other):
        return isinstance(other, LineSegment) and (self.point1, self.point2) == (other.point1, other.point2)
        
    def getRandomPoint(self):
        percentage = random.randrange(2, 99) / 100 #end points not allowed so that legal split works properly
        return self.point1 + self.vector.scaled(percentage)
        
    def getEndPoint(self):
        return self.point2
    
    def getInitialPoint(self):
        return self.point1
    
    def getMidPoint(self):
        x = (self.point1.x + self.point2.x) * 0.5
        y = (self.point1.y + self.point2.y) * 0.5
        return Point(x, y)

    def getBasis(self):
        x1, y1, x2, y2 = self.point1.x, self.point1.y, self.point2.x, self.point2.y
        dx = dy = 0
        if (x2-x1) == 0: 
            dy = (y2-y1) 
            return Vector(dx, dy).normalized()
        
        slope = abs((y2-y1)/(x2-x1))
            
        dx = 1 if x2 > x1 else -1

        dy = slope if y2 > y1 else -slope

        return Vector(dx, dy).normalized()
    
    def getLength(self):
        x1, y1, x2, y2 = self.point1.x, self.point1.y, self.point2.x, self.point2.y
        return distance(x1, y1, x2, y2)
    
    def getAntennaRays(self):
        v0 = self.vector.getOrthogonal()
        rayList = []
        for direction in [v0, v0.scaled(-1)]:
            for point in [self.point1, self.point2]:
                rayList.append(Ray(point, direction))
        return rayList
    
    def overlaps(self, other): 
        if onSameLine(self, other):
            pointMap = {self.point1.x:self.point1.y, self.point2.x:self.point2.y, other.point1.x:other.point1.y, other.point2.x:other.point2.y}
            xVals = sorted(list(pointMap.keys()))
            minX, maxX = xVals[0], xVals[len(xVals)-1]
            leftBound, rightBound = (minX, pointMap[minX]), (maxX, pointMap[maxX])
            return (self.length + other.length) >= distance(*leftBound, *rightBound)
        else:
            return False
            
    def intersects(self, other):
        vectorA, vectorB = self.vector, other.vector
        pointA, pointB = self.point1, other.point1
        M1 = Matrix_2x2(vectorA, vectorB)
        M2 = Matrix_2x2(vectorA, pointB - pointA)
        M3 = Matrix_2x2(vectorB, pointA - pointB)
        
        if almostEqual(M1.det, 0): #vectorA and vectorB are linearly dependent
            if self.overlaps(other): 
                return True
            return False

        scalarA = M3.det / M1.det
        scalarB = M2.det / (-M1.det)
    
        if (almostEqual(scalarA, 0) or almostEqual(scalarA, 1) or 0 < scalarA < 1) and (almostEqual(scalarB, 0) or almostEqual(scalarB, 1) or 0 < scalarB < 1): #endpoints count as intersection
            return True
        return False

class PuzzlePiece():
    snapDistance = 10
    pieceColors = ['red', 'orange', 'yellow', 'green', 'blue', 'indigo', 'violet']
    
    def __init__(self, points):
        self.points = copy.deepcopy(points)
        self.lines = LineSegment.getLinesFromPoints(self.points)
        self.color = random.choice(PuzzlePiece.pieceColors)
        self.border = 'black'
        
        self.selected = False
        
        self.left, self.top, self.width, self.height = getDims(self.points)
        
        self.sizeControl = min(self.width, self.height) * 0.25
        
        self.masterPoint = Point(self.left, self.top)
        self.commandVectors = self.getCommandVectors()
        
        self.area = self.getArea()
        
        self.dx = 0 
        self.dy = 0
        self.ddy = 4
        self.floor = None
        
        self.breakVector = None
    
    def __repr__(self):
        return f'''PuzzlePiece: {self.area}'''
    
    def __eq__(self, other):
        return isinstance(other, PuzzlePiece) and (set(self.points) == set(other.points)) 
    
    def getCommandVectors(self):
        V = []
        for point in self.points:
            V.append(LineSegment(self.masterPoint, point).vector)
        return V
    
    def scale(self, k):
        for vector in self.commandVectors:
            vector.x *= k 
            vector.y *= k
        self.updatePoints()
    
    def setBreakVector(self, app):
        self.breakVector = LineSegment(Point(app.width/2, app.height/2), self.masterPoint).vector.normalized()
    
    def updatePoints(self):
        for i in range(len(self.points)):
            point = self.points[i]
            commandVector = self.commandVectors[i]
            point.moveTo(self.masterPoint.x + commandVector.x , self.masterPoint.y + commandVector.y)
        self.lines = LineSegment.getLinesFromPoints(self.points)
        self.left, self.top, self.width, self.height = getDims(self.points)
    
    def moveTo(self, x, y):
        self.masterPoint.moveTo(x, y)
        self.updatePoints()
        
    def moveBy(self, dx, dy):
        self.moveTo(self.masterPoint.x+dx, self.masterPoint.y+dy)
    
    def setMasterPoint(self, x, y):
        self.masterPoint = Point(x, y)
        self.commandVectors = self.getCommandVectors()
    
    def getHintPiece(self):
        newPiece = copy.deepcopy(self)
        newPiece.color = None
        return newPiece
    
    def containsPoint(self, x, y):
        hitCount = 0
        u = Ray(Point(x, y), Vector(0, -1))
        for edge in self.lines:
            if u.point1.onLine(edge): 
                return True
            if u.hit(edge) != None:
                hitCount += 1
        
        if hitCount != 1:
            return False
        return True
    
    def containsPiece(self, other): #edges overlapping still counts 
         for point in other.points:
            if not self.containsPoint(point.x, point.y):
                return False
         return True 
    
    def getArea(self):
        anchor = self.points[0]
        area = 0
        for line in self.lines[1:-1]: 
            a = line.getLength()
            b = anchor.distance(line.getInitialPoint())
            c = anchor.distance(line.getEndPoint())
            area += HeronsFormula(a, b, c)
        return area
        
    def getRandomSplit(self, line1 = None, randomPoint1 = None, line2 = None, randomPoint2 = None):
        while line1 == None or not self.isLegalSplit(line1, randomPoint1, line2, randomPoint2):
            line1 = random.choice(self.lines)
            temp = copy.deepcopy(self.lines)
            temp.remove(line1)
            line2 = random.choice(temp)
            randomPoint1 = line1.getRandomPoint()
            randomPoint2 = line2.getRandomPoint()
            idx1 = self.lines.index(line1) 
            idx2 = self.lines.index(line2)

            if idx1 > idx2:
                line1, line2 = line2, line1
                randomPoint1, randomPoint2 = randomPoint2, randomPoint1
                idx1, idx2 = idx2, idx1
            
        return line1, randomPoint1, idx1, line2, randomPoint2, idx2
        
    def splitPiece(self, line1, randomPoint1, idx1, line2, randomPoint2, idx2):
        half1 = self.lines[idx1:idx2]
        half2 = self.lines[idx2:] + self.lines[:idx1]
        Piece1_points = [randomPoint1] + [line.getEndPoint() for line in half1] + [randomPoint2]
        Piece2_points = [randomPoint2] + [line.getEndPoint() for line in half2] + [randomPoint1]
        return PuzzlePiece(Piece1_points), PuzzlePiece(Piece2_points)
    
    def isLegalSplit(self, line1, randomPoint1, line2, randomPoint2):
        randomLine = LineSegment(randomPoint1, randomPoint2)
        if PuzzlePiece.lineIsFullyInOut(self.lines, randomLine, line1, line2) and self.lineInPolygon(randomLine) and PuzzlePiece.piecesAreSufficientlyLarge(self.lines, randomLine, self.sizeControl):
            return True
        return False
        
    @staticmethod
    def lineIsFullyInOut(lines, line, line1, line2):
        for edge in lines:
            if line.intersects(edge) and edge != line1 and edge != line2:
                return False 
        return True
                
    def lineInPolygon(self, line): 
        return self.containsPoint(*line.getMidPoint().unpack())
    
    @staticmethod
    def piecesAreSufficientlyLarge(lines, line, sizeControl):
        ref = line.getMidPoint()
        u = Ray(ref, line.vector.getOrthogonal())
        v = Ray(ref, line.vector.getOrthogonal().scaled(-1))
        for edge in lines:
            if (u.hit(edge) != None and u.hit(edge)[0] < sizeControl) or (v.hit(edge) != None and v.hit(edge)[0] < sizeControl):
                return False 
        return True
    
    def drop(self):
        self.moveBy(0, self.dy) 
        self.dy += self.ddy 
        if self.top + self.height >= self.floor:
            err = self.floor - (self.top+self.height)
            self.moveBy(0, err)
            self.dy *= -0.5
        
    def shatter(self):
        self.moveBy(self.breakVector.x*20, self.breakVector.y*20)

class Base(PuzzlePiece):
    minBaseSides, maxBaseSides = 5, 15
    minBaseRadius, maxBaseRadius = 125, 200
    
    def __init__(self, app):
        self.points = Base.generateBasePoints(app)
        self.lines = LineSegment.getLinesFromPoints(self.points)
        self.left, self.top, self.width, self.height = getDims(self.points)
        
        self.masterPoint = Point(self.left+self.width/2, self.top+self.height/2)
        self.commandVectors = self.getCommandVectors()

        self.centerBase(app)
        
        self.color = None 
        self.border = 'black'
        
        self.sizeControl = min(self.width, self.height) * 0.25
        
        self.area = self.getArea()
    
    def __repr__(self):
        return f'''Base: points = {self.points}'''
    
    def centerBase(self, app):
        self.moveTo(app.width/2, app.height/2)

    @staticmethod
    def generateBasePoints(app):
        points = []
        percentages = [i/100 for i in range(101)]
        baseSides = random.randrange(Base.minBaseSides, Base.maxBaseSides+1)
        for _ in range(baseSides):
            percentage = random.choice(percentages)
            baseRadius = random.randrange(Base.minBaseRadius, Base.maxBaseRadius+1, 25)
            angle = 2*math.pi*percentage
            currPoint = Base.getPointFromAngle(app.width/2, app.height/2, baseRadius, angle)
            points.append(currPoint)
            percentages.remove(percentage)
        
        return sorted(points)
        
    @staticmethod
    def getPointFromAngle(cx, cy, radius, theta): #theta in radians
        x, y = radius*math.cos(theta) + cx, -radius*math.sin(theta) + cy
        return Point(x, y, theta)
        
class Puzzle():
    maxPuzzlePieces = 16#must be a power of 2 due to recursiveSplit having two recursive calls per level
    minPuzzlePieces = 5
    snapDistance = 100
    
    def __init__(self, app):
        self.base = Base(app)
        self.puzzlePieces = []
        while len(self.puzzlePieces) < Puzzle.minPuzzlePieces:
            self.puzzlePieces = Puzzle.recursiveSplit(self.base, math.log2(Puzzle.maxPuzzlePieces))
        self.hintPieces = [piece.getHintPiece() for piece in self.puzzlePieces]
        self.randomlyDistributePuzzlePieces(app)
        
        self.placed = []
        self.progress = self.getProgress()
    
    def __repr__(self):
        return f'''Puzzle: Base = {self.base},
        
        PuzzlePieces = {self.puzzlePieces},
        
        HintPieces = {self.hintPieces},
        
        solved = {self.solved}'''
        
    def randomlyDistributePuzzlePieces(self, app):
        for piece in self.puzzlePieces:
            x = random.randrange(0, math.floor(app.width-piece.width))
            y = random.randrange(0, math.floor(app.height-piece.height))
            piece.moveTo(x, y)
            piece.floor = piece.top + piece.height
            piece.moveTo(x, -app.height/2)
    
    def solved(self):
        return len(self.puzzlePieces) == len(self.placed)
    
    def solveManager(self):
        if self.puzzleSolved():
            self.solved = True
    
    def selectionManager(self, mouseX, mouseY): #on mouse press
        for i in range(1, len(self.puzzlePieces)+1):
            piece = self.puzzlePieces[-i]
            if piece.containsPoint(mouseX, mouseY):
                moveToFront(piece, self.puzzlePieces)
                piece.setMasterPoint(mouseX, mouseY)
                piece.selected = True
                piece.border = 'red'
                
                if piece in self.placed:
                    self.placed.remove(piece)
                self.progress = self.getProgress()
                return 
    
    def dragManager(self, mouseX, mouseY): #on mouse move
        mostRecent = self.puzzlePieces[-1]
        if mostRecent.selected:
            mostRecent.moveTo(mouseX, mouseY)
    
    def dropManager(self, mouseX, mouseY): #on mouse release, remember to code snapping functionality
        mostRecent = self.puzzlePieces[-1]
        mostRecent.selected = False
        mostRecent.border = 'black'
        self.snap(mostRecent)
    
    def snap(self, mostRecent):
        moves = self.getPossibleSnaps(mostRecent)
        for move in moves: #move is a vector
            mostRecent.moveBy(move.x, move.y)
            if self.isLegalMove(mostRecent):
                self.placed.append(mostRecent)
                self.progress = self.getProgress()
                return
            mostRecent.moveBy(-move.x, -move.y)
    
    def isLegalMove(self, temp):
        if not self.base.containsPiece(temp):
            return False
        for piece in self.placed:
            if piece.containsPiece(temp):
                return False
        return True
    
    def getPossibleSnaps(self, mostRecent):
        directSnaps = set()
        cornerSnaps = set()
        for currEdge in mostRecent.lines:
            for ray in currEdge.antennaRays:
                for piece in self.placed:
                    for pieceEdge in piece.lines:
                            Puzzle.updateSnaps(directSnaps, cornerSnaps, currEdge, pieceEdge, ray)
                for baseEdge in self.base.lines: 
                    Puzzle.updateSnaps(directSnaps, cornerSnaps, currEdge, baseEdge, ray)
        
        return sorted(cornerSnaps) + sorted(directSnaps)
    
    def getPossibleMoves(self, piece):
        moves = set()
        for currEdge in piece.lines:
            for placed in self.placed:
                for extEdge in placed.lines:
                    Puzzle.updateMoves(moves, currEdge, extEdge)
            for baseEdge in self.base.lines:
                Puzzle.updateMoves(moves, currEdge, baseEdge)
        
        return sorted(moves)
    
    @staticmethod
    def updateSnaps(directSnaps, cornerSnaps, currEdge, extEdge, ray):
        point = ray.point1
        hit = ray.hit(extEdge)
        M = Matrix_2x2(currEdge.vector, extEdge.vector)
        if almostEqual(M.det, 0):
            if hit != None:
                a = extEdge.point1 + extEdge.vector.scaled(hit[1])
                A = point.distance(a)
                if A < Puzzle.snapDistance: 
                    directSnaps.add(Vector(a.x - point.x, a.y - point.y))
    
            b, c = extEdge.point1, extEdge.point2
            B, C = point.distance(b), point.distance(c)
            if B < Puzzle.snapDistance:
                cornerSnaps.add(Vector(b.x - point.x, b.y - point.y))
            if C < Puzzle.snapDistance:
                cornerSnaps.add(Vector(c.x - point.x, c.y - point.y))
    
        
    @staticmethod
    def updateMoves(moves, currEdge, extEdge):
        if parallel(currEdge, extEdge):
            p1, p2, p3, p4 = currEdge.getInitialPoint(), extEdge.getInitialPoint(), currEdge.getEndPoint(), extEdge.getEndPoint()
            move1 = Vector(p2.x-p1.x, p2.y-p1.y)
            move2 = Vector(p4.x-p3.x, p4.y-p3.y)
            moves.add(move1)
            moves.add(move2)

    def getProgress(self):
        total = self.base.area 
        filled = 0 
        for piece in self.placed: 
            filled += piece.area
        
        return math.ceil((filled/total) * 100)
    
    @staticmethod
    def recursiveSplit(piece, levelsLeft, split = True):
        if not split or levelsLeft == 0:
            return [piece]
        else:
            splitData = piece.getRandomSplit()
            piece1, piece2 = piece.splitPiece(*splitData)
            split1, split2 = bool(random.randrange(0,4)), bool(random.randrange(0,4))
            return Puzzle.recursiveSplit(piece1, levelsLeft-1, split1) + Puzzle.recursiveSplit(piece2, levelsLeft-1, split2)
            
    @staticmethod
    def recursiveSolver(app):
        print(len(app.puzzle.puzzlePieces))
        for piece in app.puzzle.puzzlePieces:
            piece.moveTo(300, -600)
        app.puzzle.liveBacktracking(app)
    
    def liveBacktracking(self, app):
        if self.solved():
            return self
        else:
            for i in range(len(self.puzzlePieces)):
                piece = self.puzzlePieces[i]
                for move in self.getPossibleMoves(piece):
                    piece.moveBy(move.x, move.y)
                    if self.isLegalMove(piece):
                        print('yay')
                        self.placed.append(piece)
                        self.progress = self.getProgress()
                        self.puzzlePieces.pop(i)
                        solution = self.liveBacktracking(app)
                        if solution != None:
                            return solution
                        self.puzzlePieces.insert(i, self.placed.pop())
                        self.progress = self.getProgress()
                    print('boo')
                    piece.moveBy(-move.x, -move.y)
                    
            return None 
        
    def dropPieces(self, app):
        for piece in self.puzzlePieces:
            piece.drop()
        
        app.timer += 1
        if app.timer % 70 == 0:
            app.dropPieces = False
    
    def setBreakVectors(self, app):
        for piece in self.puzzlePieces:
            piece.setBreakVector(app)
    
    def breakPieces(self, app):
        for piece in self.puzzlePieces: 
            piece.shatter()
            piece.scale(1.065)

        app.timer += 1
        if app.timer % 70 == 0:
            app.gameOver = False
                                
def onAppStart(app):
    app.width = 600
    app.height = 600
    newGame(app)
    app.stepsPerSecond = 60
    
def newGame(app):
    app.puzzle = Puzzle(app)
    app.showHint = False
    app.gameOver = False
    app.dropPieces = True
    app.timer = 0

def redrawAll(app):
    drawPiece(app.puzzle.base)
    for piece in app.puzzle.puzzlePieces:
        drawPiece(piece)
    if app.showHint:
        for piece in app.puzzle.hintPieces:
            drawPiece(piece)
    if app.gameOver:
        drawLabel('SOLVED!', 300, 100)
        app.puzzle.progress = 100 
    drawLabel(f'{app.puzzle.progress}% Complete', 300, 50)

def drawPiece(piece):
    points = []
    for point in piece.points:
        points += point.unpack()
    drawPolygon(*points, fill = piece.color, border = piece.border)

def onKeyPress(app, key):
    if key == 'h': app.showHint = not app.showHint
    elif key == 'n':
        newGame(app)
        
def onMousePress(app, mouseX, mouseY):
    if not app.dropPieces:
        app.puzzle.selectionManager(mouseX, mouseY)

def onMouseDrag(app, mouseX, mouseY):
    if not app.dropPieces:
        app.puzzle.dragManager(mouseX, mouseY)

def onMouseRelease(app, mouseX ,mouseY):
    if not app.dropPieces:
        app.puzzle.dropManager(mouseX, mouseY)
        if app.puzzle.solved(): 
            app.gameOver = True
            app.puzzle.setBreakVectors(app)
            app.timer = 0

def onStep(app):
    if app.dropPieces:
        app.puzzle.dropPieces(app)
    
    if app.gameOver:
        app.puzzle.breakPieces(app)
        

def main():
    runApp()
main()