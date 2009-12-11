module Main where
{-
A simple module to test how long it takes to build up a tree.
The test data file is taken from Facebook 
http://www.facebook.com/careers/puzzles.php?puzzle_id=17

Thanks to Wei Hu (weihu@cs.virginia.edu) for alerting me about the
slowness of my previous implementation.

I also have another implementation of bktrees in the file BKTree which
I can use to benchmark against.

-}

import Data.Set.BKTree

import BKTree

main = do file <- readFile "twl06.txt"
          print (size (fromList (lines file)))

