module Main where

import Quickhull
import System.Environment
import Data.Array.Accelerate (toList, fromList, (:.)(..), Z(..))
import Data.List (sortOn)
import Control.Monad

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> do
      putStrLn "No input files were given."
      putStrLn "You should pass one or more input files through the command line."
      putStrLn "Example:"
      putStrLn "  stack run -- input/small.in"
    _ -> mapM_ run args

run :: FilePath -> IO ()
run path = do
  input <- readInput $ path

  let veryLarge = length input > 80000

  putStrLn $ "Input: " ++ show path

  if veryLarge then
    putStrLn $ "Set of " ++ show (length input) ++ " points"
  else
    printPoints input

  let output = toList $ quickhull $ fromList (Z :. length input) input
  putStrLn "Output:"
  if veryLarge then
    putStrLn $ "Set of " ++ show (length output) ++ " points"
  else
    printPoints output

readInput :: FilePath -> IO [Point]
readInput path = do
  input <- readFile path
  return $ map (f . words) $ lines input
  where
    f [x, y] = (read x, read y)
    f _ = error "readInput: wrong input"

printPoints :: [Point] -> IO ()
printPoints [] = putStrLn "[]"
printPoints points' = when (length points' < 100) (print points') >> putStrLn "" >> printPoints' minX maxY points
  where
    points = sortOn (\(x, y) -> (-y, x)) points'

    maxY = snd $ head points
    minX = foldl min maxBound $ map fst points

    printPoints' :: Int -> Int -> [Point] -> IO ()
    printPoints' _ _ [] = putStr "\n\n"
    printPoints' cx cy ((x, y) : pts)
      | cy == y && cx > x = printPoints' (x + 1) cy pts
      | cy == y           = putStr (replicate (x - cx) ' ') >> putStr "o" >> printPoints' (x + 1) cy pts
      | otherwise         = putStrLn "" >> printPoints' minX (cy - 1) ((x, y) : pts)

-- [(-1,2),(0,1),(-4,0),(2,0),(-2,-1),(1,-1),(-1,3),(0,3)]
-- [(-4,0),(-1,2),(0,1),(-1,3),(0,3),(-4,0),(-2,-1),(1,-1),(-4,0)]