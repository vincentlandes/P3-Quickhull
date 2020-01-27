{-# LANGUAGE TypeOperators #-}

module Quickhull
    ( quickhull
    , Point
    , propagateR
    , segmentedPostscanr
    ) where

import Data.Array.Accelerate
import qualified Data.Array.Accelerate.Unsafe as Unsafe
import qualified Prelude as P

-- Accelerate backend
import Data.Array.Accelerate.Interpreter
-- import Data.Array.Accelerate.LLVM.Native
-- import Data.Array.Accelerate.LLVM.PTX

type Point = (Int, Int)

type Line = (Point, Point)

type SegmentedPoints = (Vector Bool, Vector Point)

input1 :: Acc (Vector Point)
input1 = use $ fromList (Z :. 15) [(1,4),(8,19),(5,9),(7,9),(4,2),(3,9),(9,16),(1,5),(9,11),(4,0),(8,18),(8,7),(7,18),(6,18),(4,19)]

input3 :: Acc (Vector Point)
input3 = use $ fromList (Z :. 200) [(31 ,17), (23 ,36), (23, 7), (16 ,24), (35 ,27), (42 ,17), (13 ,39), (31 ,25), (34 ,26), (41 ,40), (43 ,11), (33 ,31), (34 ,42), (36 ,47), (12 ,14), (44 ,20), (36 ,34), (49 ,20), (22 ,23), (47 ,29), (36 ,26), (30 ,44), (30 ,35), (4 ,17), (23 ,32), (42 ,13), (39 ,44), (18 ,18), (28 ,43), (5 ,25), (14 ,24), (6 ,19), (12 ,31), (11 ,34), (21 ,26), (45 ,12), (47 ,26), (14 ,40), (23 ,25), (12 ,35), (3 ,19), (23 ,13), (7, 9), (25 ,31), (8 ,12), (34 ,43), (15, 9), (40 ,30), (25, 0), (22 ,32), (40 ,18), (1 ,18), (11 ,42), (1 ,26), (20 ,13), (35 ,16), (8 ,26), (12 ,13), (33 ,43), (22 ,44), (36 ,38), (15 ,44), (26 ,38), (41 ,30), (31, 2), (23 ,22), (40 ,27), (44 ,14), (42 ,43), (28 ,28), (14 ,19), (36 ,30), (43 ,25), (49 ,26), (29 ,19), (13 ,10), (28 ,23), (4 ,32), (24 ,35), (42 ,12), (22 ,18), (15 ,10), (31 ,15), (35 ,39), (36 ,17), (41 ,21), (39 ,39), (19 ,26), (36 ,28), (27 ,35), (14 ,10), (14 ,23), (31 ,13), (27 ,34), (14 ,35), (29, 6), (24 ,19), (31 ,47), (1 ,25), (31 ,31), (6 ,14), (23 ,24), (8 ,43), (1 ,19), (22 ,31), (43 ,42), (33 ,28), (28, 5), (39, 6), (32 ,28), (29, 9), (34 ,31), (5 ,16), (28 ,15), (26 ,49), (27 ,44), (18 ,31), (9 ,26), (37 ,18), (32 ,18), (24 ,20), (10 ,39), (11 ,31), (43 ,27), (37 ,45), (42 ,37), (20, 4), (13 ,35), (5 ,27), (28 ,14), (25 ,27), (8 ,35), (43 ,30), (14 ,44), (6 ,16), (36 ,31), (49 ,21), (45 ,14), (26, 3), (38 ,40), (33 ,41), (4 ,37), (20 ,26), (36, 9), (32, 9), (27 ,40), (32 ,26), (2 ,33), (13, 8), (26 ,45), (35 ,45), (44 ,29), (34 ,34), (29 ,15), (41 ,10), (38 ,30), (30 ,33), (22, 9), (46 ,28), (21 ,42), (26 ,32), (3 ,14), (5 ,28), (37 ,16), (38 ,27), (15, 5), (29 ,49), (44 ,17), (34 ,44), (36 ,19), (44 ,10), (32 ,45), (33 ,35), (14 ,15), (35 ,28), (36 ,35), (28 ,37), (34 ,32), (41 ,43), (41 ,22), (29, 4), (20 ,25), (36 ,13), (14 ,30), (43 ,35), (22 ,17), (28, 7), (8 ,30), (10 ,30), (46 ,23), (19 ,39), (32 ,33), (13 ,12), (16 ,20), (6 ,11), (33 ,17), (34 ,18), (29 ,35), (8 ,23), (44 ,23)]

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

-- * Exercise 1
leftMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
leftMostPoint points = fold min (T2 maxBound maxBound) points

rightMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
rightMostPoint points = fold max (T2 minBound minBound) points

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
    p1 = the $ leftMostPoint points
    p2 = the $ rightMostPoint points
    line = T2 p1 p2

    -- * Exercise 2
    isUpper :: Acc (Vector Bool)
    isUpper = map (pointIsLeftOfLine line) points

    isLower :: Acc (Vector Bool)
    isLower = zipWith (\x y -> (x /= p1 && x /= p2 && not y)) points isUpper --zipwith, 2 arrays, samenvoegen met labda functie zodat p1 EN p2 niet in deze lijst zitten.

    -- * Exercise 3
    lowerIndices :: Acc (Vector Int)
    lowerIndices = prescanl (+) 0 (map boolToInt isLower)

    -- * Exercise 4
    upperIndices :: Acc (Vector Int)
    countUpper :: Acc (Scalar Int)
    T2 upperIndices countUpper = scanl' (+) 0 (map boolToInt isUpper)

    -- * Exercise 5
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Point -> Exp Bool -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f p upper idxLower idxUpper
          = p == p1 ? ( index1 0
          , p == p2 ? ( index1 (count + 1)
          , upper   ? ( index1 (idxUpper + 1)
          ,             index1 (count + idxLower + 2) )))
            where count = the countUpper
      in
        zipWith4 f points isUpper lowerIndices upperIndices
        
    
    -- * Exercise 6
    empty :: Acc (Vector Point)
    --empty = fill (constant (Z:.(unlift (length points)))) p1
    empty = fill (index1 (length points +1)) p1

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 7
    headFlags :: Acc (Vector Bool)
    headFlags = map (\x-> x == p1 || x == p2) newPoints
  in
    T2 headFlags newPoints
    --error $ P.show $ run headFlags

-- * Exercise 8
segmentedPostscanl :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanl operator headFlags points = map snd (postscanl (segmentedL operator) Unsafe.undef (zip headFlags points))

segmentedPostscanr :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanr operator headFlags points = map snd (postscanr (segmentedR operator) Unsafe.undef (zip headFlags points))

segmentedL op (T2 fx x) (T2 fy y) = T2 ( fx || fy ) ( fy ? (y, op x y))
segmentedR op (T2 fx x) (T2 fy y) = T2 ( fx || fy ) ( fx ? (x, op x y))


-- * Exercise 9
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedPostscanl const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedPostscanr (P.flip const)

-- * Exercise 10
propagateLine :: Acc SegmentedPoints -> Acc (Vector Line)
propagateLine (T2 headFlags points) = zip vecP1 vecP2
  where
    vecP1 = propagateL headFlags points
    vecP2 = propagateR headFlags points

-- * Exercise 11
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = prescanr (\x y -> x) (lift False) flags

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = prescanl (\x y -> y) (lift False) flags

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    vecLine :: Acc (Vector Line)
    vecLine = propagateLine (T2 headFlags points)

    headFlagsL = shiftHeadFlagsL headFlags
    headFlagsR = shiftHeadFlagsR headFlags

    -- * Exercise 12
    furthest :: Acc (Vector Point)
    furthest = map snd $ propagateR headFlagsL $ segmentedPostscanl max headFlags distance 
      where distance = zip (zipWith nonNormalizedDistance vecLine points) points

    -- * Exercise 13
    isLeft :: Acc (Vector Bool)
    isLeft = zipWith pointIsLeftOfLine linesL points
      where linesL = zip (map fst vecLine) furthest
    
    isRight :: Acc (Vector Bool)
    isRight = zipWith pointIsLeftOfLine linesR points
    linesR = zip furthest (map snd vecLine)

    -- * Exercise 14
    segmentIdxLeft :: Acc (Vector Int)
    segmentIdxLeft = segmentedPostscanl (+) headFlags (map boolToInt isLeft)

    segmentIdxRight :: Acc (Vector Int)
    segmentIdxRight = segmentedPostscanl (+) headFlags (map boolToInt isRight)

    -- * Exercise 15
    countLeft :: Acc (Vector Int)
    countLeft = segmentedPostscanr max headFlags segmentIdxLeft

    -- * Exercise 16
    segmentSize :: Acc (Vector Int)
    segmentSize = zipWith3 (\x y z -> x ? (1 , y ? (z+1, 0))) headFlags (shiftHeadFlagsL headFlags) segmentLR

    segmentLR = zipWith (+) segmentIdxLeft segmentIdxRight

    segmentOffset :: Acc (Vector Int)
    size :: Acc (Scalar Int)
    T2 segmentOffset size = scanl' (+) 0 segmentSize

    -- * Exercise 17
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Bool -> Exp Point -> Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f flag p furthestP left right offset cntLeft idxLeft idxRight
          = flag ? (index1 offset
            , left ? (index1 (offset + idxLeft - 1)
            , right ? (index1 (offset + idxRight + 1)
            , p == furthestP ? (index1 (offset + cntLeft)
            , ignore))))
      in
        zipWith9 f headFlags points furthest isLeft isRight segmentOffset countLeft segmentIdxLeft segmentIdxRight

    -- * Exercise 18
    empty :: Acc (Vector Point)
    empty = fill (index1 $ the size) $ T2 0 0

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 19
    newHeadFlags :: Acc (Vector Bool)
    newHeadFlags = permute const (fill (index1 $ the size) $ lift False) (permutation2 !) (fill (shape points) $ lift True)

    permutation2 :: Acc (Vector (Z :. Int))
    permutation2 =
      let
        f :: Exp Bool -> Exp Point -> Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f flag p furthestP left right offset cntLeft idxLeft idxRight
          = flag ? (index1 offset
            , p == furthestP ? (index1 (offset + cntLeft)
            , ignore))
      in
        zipWith9 f headFlags points furthest isLeft isRight segmentOffset countLeft segmentIdxLeft segmentIdxRight    

    -- temp1 = zipWith3 (\x y z -> x ? (lift True, ((not (lift y)) && (not( lift z)) ? (lift True, lift False)))) headFlags isLeft isRight
    -- temp2 = zip3 points furthest temp1
    -- temp3 = filter (\x@(p1,p2,b) -> p1 == p2 ? (lift False, lift True)) temp2
  in
    T2 newHeadFlags newPoints
    --error $ P.show $ run newPoints

-- * Exercise 20
condition:: Acc SegmentedPoints -> Acc (Scalar Bool)
condition (T2 f _) = unit $ not $ the $ all (== lift True) f

-- * Exercise 21
quickhull' :: Acc (Vector Point) -> Acc (Vector Point)
quickhull' points = asnd $ awhile condition partition segPoints
  where segPoints = initialPartition points

quickhull :: Vector Point -> Vector Point
quickhull = run1 quickhull'

-- * Bonus
quickhullSort' :: Acc (Vector Int) -> Acc (Vector Int)
quickhullSort' = undefined

quickhullSort :: Vector Int -> Vector Int
quickhullSort = run1 quickhullSort'
