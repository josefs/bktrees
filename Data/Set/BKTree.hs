{- | 
   Module      : Data.Set.BKTree
   Copyright   : (c) Josef Svenningsson 2007
                 (c) Henning Günter     2007
   License     : BSD-style
   Maintainer  : josef.svenningsson@gmail.com
   Stability   : Alpha quality. Interface may change without notice.
   Portability : portable

   Burkhard-Keller trees provide an implementation of sets which apart
   from the ordinary operations also has an approximate member search,
   allowing you to search for elements that are of a distance @n@ from
   the element you are searching for. The distance is determined using
   a metric on the type of elements. Therefore all elements must
   implement the 'Metric' type class, rather than the more usual
   'Ord'.

   Useful metrics include the manhattan distance between two points,
   the Levenshtein edit distance between two strings, the number of
   edges in the shortest path between two nodes in an undirected graph
   and the Hamming distance between two binary strings. Any euclidean
   space also has a metric. However, in this module we use int-valued
   metrics and that's not compatible with the metrics of euclidean 
   spaces which are real-values.

   The worst case complexity of many of these operations is quite bad,
   but the expected behavior varies greatly with the metric. For
   example, the discrete metric (@distance x y | y == x = 0 |
   otherwise = 1@) makes BK-trees behave abysmally. The metrics
   mentioned above should give good performance characteristics.

-}
module Data.Set.BKTree 
    (-- The main type
     BKTree
     -- Metric
    ,Metric(..)
     --
    ,null,size,empty
    ,fromList,singleton
    ,insert
    ,member,memberDistance
    ,delete
    ,union,unions
    ,elems,elemsDistance
    ,closest
#ifdef DEBUG
    ,runTests
#endif
    )where

import qualified Data.IntMap as M
import qualified Data.List as L hiding (null)
import Prelude hiding (null)

import Data.Array.IArray (Array,array,listArray,(!),assocs)
import Data.Array.Unboxed (UArray)

#ifdef DEBUG
import qualified Prelude
import Test.QuickCheck
import Text.Printf
import System.Exit
#endif

-- | A type is 'Metric' if is has a function 'distance' which has the following
-- properties:
--
-- * @'distance' x y >= 0@
--
-- * @'distance' x y == 0@ if and only if @x == y@
--
-- * @'distance' x y == 'distance' y x@
--
-- * @'distance' x z <= 'distance' x y + 'distance' y z@
--
-- All types of elements to 'BKTree' must implement 'Metric'.
--
-- This definition of a metric deviates from the mathematical one in that it
-- returns an integer instead of a real number. The reason for choosing 
-- integers is that I wanted to avoid the rather unpredictable rounding
-- of floating point numbers.
class Eq a => Metric a where
  distance :: a -> a -> Int

instance Metric Int where
  distance i j = abs (i - j)

-- Fishy instance. Maybe I shouldn't have it. 
-- Or generalize Metric to use integer?
instance Metric Integer where
  distance i j = fromInteger (abs (i - j))

instance Metric Char where
  distance i j = abs (fromEnum i - fromEnum j)

hirschberg :: Eq a => [a] -> [a] -> Int
hirschberg xs [] = length xs
hirschberg xs ys = let
	lxs = length xs
	lys = length ys
	start_arr :: UArray Int Int
	start_arr = listArray (1,lys) [1..lys]
	in (L.foldl' (\arr (i,xi) -> let
		narr :: UArray Int Int
		narr = array (1,lys) (snd $ L.mapAccumL
			(\(s,c) ((j,el),yj) -> let
				nc = minimum
					[s  + (if xi==yj then 0 else 1)
					,el + 1
					,c  + 1
					]
				in ((el,nc),(j,nc)))
			(i-1,i)
			(zip (assocs arr) ys)
			)
		in narr
		) start_arr (zip [1..] xs))!lys


instance Eq a => Metric [a] where
  distance = hirschberg

-- --------
-- BKTrees
-- --------

-- | The type of Burkhard-Keller trees.
data BKTree a = Node a !Int (M.IntMap (BKTree a))
              | Empty
#ifdef DEBUG
                deriving Show
#endif


-- | Test if the tree is empty.
null :: BKTree a -> Bool
null (Empty)    = True
null (Node _ _ _) = False

-- | Size of the tree.
size :: BKTree a -> Int
size (Empty) = 0
size (Node _ s _) = s

-- | The empty tree.
empty :: BKTree a
empty = Empty

-- | The tree with a single element
singleton :: a -> BKTree a
singleton a = Node a 1 M.empty

-- | Inserts an element into the tree. If an element is inserted several times
--   it will be stored several times.
insert :: Metric a => a -> BKTree a -> BKTree a
insert a Empty = Node a 1 M.empty
insert a (Node b size map) = Node b (size+1) map'
  where map' = M.insertWith recurse d (Node a 1 M.empty) map
        d    = distance a b
        recurse _ tree = insert a tree

-- | Checks whether an element is in the tree.
member :: Metric a => a -> BKTree a -> Bool
member a Empty = False
member a (Node b _ map) 
    | d == 0    = True
    | otherwise = case M.lookup d map of
                    Nothing -> False
                    Just tree -> member a tree
    where d = distance a b

-- | Approximate searching. @'memberDistance' n a tree@ will return true if
--   there is an element in @tree@ which has a 'distance' less than or equal to
--   @n@ from @a@.
memberDistance :: Metric a => Int -> a -> BKTree a -> Bool
memberDistance n a Empty = False
memberDistance n a (Node b _ map)
    | d <= n    = True
    | otherwise = any (memberDistance n a) (M.elems subMap)
    where d = distance a b
          subMap = case M.split (d-n-1) map of
                     (_,mapRight) ->
                         case M.split (d+n+1) mapRight of
                          (mapCenter,_) -> mapCenter

-- | Removes an element from the tree. If an element occurs several times in 
--   the tree then only one occurrence will be deleted.
delete :: Metric a => a -> BKTree a -> BKTree a
delete a Empty = Empty
delete a t@(Node b _ map) 
    | d == 0    = unions (M.elems map)
    | otherwise = Node b sz subtrees
    where d = distance a b
          subtrees = M.update (Just . delete a) d map
          sz = sum (L.map size (M.elems subtrees)) + 1

-- | Returns all the elements of the tree
elems :: BKTree a -> [a]
elems Empty = []
elems (Node a _ imap) = a : concatMap elems (M.elems imap)

-- | @'elemsDistance' n a tree@ returns all the elements in @tree@ which are 
--   at a 'distance' less than or equal to @n@ from the element @a@.
elemsDistance :: Metric a => Int -> a -> BKTree a -> [a]
elemsDistance n a Empty = []
elemsDistance n a (Node b _ imap) 
    = (if d <= n then (b :) else id) $
      concatMap (elemsDistance n a) (M.elems subMap)
    where d = distance a b
          subMap = case M.split (d-n-1) imap of
                     (_,mapRight) -> 
                         case M.split (d+n+1) mapRight of
                           (mapCenter,_) -> mapCenter

-- | Constructs a tree from a list
fromList :: Metric a => [a] -> BKTree a
fromList xs = constructTree (\a -> Just (a,[])) xs

constructTree extract [] = Empty
constructTree extract (a:as)
    = case extract a of
        Nothing -> constructTree extract as
        Just (piv,rest) -> 
            (\imap -> Node piv (1 + sum (map size (M.elems imap))) imap) $
            M.fromAscList $
            map recurse $
            L.groupBy ((==) `on` fst) $
            L.sortBy (compare `on` fst) $
            concatMap (mkDist piv) $
            as ++ rest
  where mkDist piv m = case extract m of
                         Just (a,_) -> [(distance piv a,m)]
                         Nothing    -> []
        recurse bs@((k,_):_) = (k, constructTree extract (map snd bs))

-- | Merges several trees
unions :: Metric a => [BKTree a] -> BKTree a
unions xs = fromList $ concat $ map elems xs

-- | Merges two trees
union :: Metric a => BKTree a -> BKTree a -> BKTree a
union t1 t2 = unions [t1,t2]

-- | @'closest' a tree@ returns the element in @tree@ which is closest to
--   @a@ together with the distance. Returns @Nothing@ if the tree is empty.
closest :: Metric a => a -> BKTree a -> Maybe (a,Int)
closest a Empty = Nothing
closest a tree@(Node b _ _) = Just (closeLoop a (b,distance a b) tree)

closeLoop a candidate Empty     = candidate
closeLoop a candidate@(b,d) (Node x _ imap)
    = L.foldl' (closeLoop a) newCand (M.elems subMap)
    where newCand = if j >= d 
                    then candidate
                    else (x,j)
          j = distance a x
          subMap = case M.split (d-j-1) imap of
                     (_,mapRight) -> 
                         case M.split (d+j+1) mapRight of
                           (mapCenter,_) -> mapCenter

-- Helper functions

on rel f x y = rel (f x) (f y)

#ifdef DEBUG
-- Testing
-- N.B. This code requires QuickCheck 2.0

{- Testing using algebraic specification. The idea is that we have this
naive inefficient distance function. But instead of comparing it to our actual
implementation we take each clause in the definition and make it into an 
equation. We also change each occurrence of the name naive to a call to the
distance function.

naive []     ys     = length ys
naive xs     []     = length xs
naive (x:xs) (y:ys) | x == y = naive xs ys
naive (x:xs) (y:ys) = 1 + minimum [naive (x:xs) ys
                                  ,naive (x:xs) (x:ys)
                                  ,naive xs (y:ys)]

For example, the third clause becomes:
distance (x:xs) (x:ys) == distance xs ys

That way we can construct a quickCheck property from it. So, one property for
each equation in the naive algorithm. Pretty sweet! Credits go to Koen.
-}

-- Way too inefficient!
-- prop_naive xs ys = distance xs ys == naive xs (ys :: [Int])

prop_naiveEmpty xs = 
    distance [] xs == length xs &&
    distance xs [] == length (xs::[Int])
prop_naiveCons x xs ys = distance (x:xs) (x:ys) == distance xs (ys::[Int])
prop_naiveDiff x y xs ys = x /= y ==>
    distance (x:xs) (y:ys) ==
    1 + minimum [distance (x:xs) (ys :: [Int])
                ,distance (x:xs) (x:ys)
                ,distance xs (y:ys)]

-- ----------------------------------------------------
-- Semantics of BKTrees. Just a boring list of integers
sem tree = L.sort (elems tree) :: [Int]

-- For testing functions that transform trees
trans f xs = sem (f (fromList xs))

invariant t = inv [] t

inv dict Empty = True
inv dict (Node a _ imap) 
    = all (\ (d,b) -> distance a b == d) dict &&
      all (\ (d,t) -> inv ((d,a):dict) t) (M.toList imap)

-- Tests for individual functions

prop_empty n = not (member (n::Int) empty)

prop_null xs = null (fromList xs) == Prelude.null (xs :: [Int])

prop_singleton n = elems (fromList [n]) == [n :: Int]

prop_fromList xs = sem (fromList xs) == L.sort xs

prop_fromListInv xs = invariant (fromList (xs :: [Int]))

prop_insert n xs = 
    trans (insert n) xs == L.sort (n:xs)

prop_insertInv n xs =
    invariant (insert n (fromList (xs :: [Int])))

prop_member n xs = member n (fromList xs) == L.elem (n::Int) xs

prop_memberDistance dist n xs = 
 let d   = dist `mod` 5
     ref = L.any (\e -> distance n e <= d) xs
 in collect ref $
 memberDistance d n (fromList xs) == 
 L.any (\e -> distance n e <= d) (xs :: [Int])

prop_delete n xs =
  trans (delete n) xs  == 
  L.sort (removeFirst (xs :: [Int]))
 where removeFirst [] = []
       removeFirst (a:as) | a == n    = as
                          | otherwise = a : removeFirst as

prop_deleteInv n xs =
    invariant (delete n (fromList (xs :: [Int])))

prop_elems xs = L.sort (elems (fromList xs)) == L.sort (xs::[Int])

prop_elemsDistance dist n xs = 
  let d = dist `mod` 5 in
  L.sort (elemsDistance d n (fromList xs)) == 
  L.sort (filter (\e -> distance n e <= d) (xs::[Int]))

prop_unions xss = 
    sem (unions (map fromList xss)) == 
    L.sort (concat (xss::[[Int]]))

prop_unionsInv xss =
    invariant (unions (map fromList (xss :: [[Int]])))

prop_union xs ys =
    sem (union (fromList xs) (fromList ys)) ==
    L.sort (xs ++ (ys::[Int]))

prop_unionInv xs ys =
    invariant (union (fromList (xs :: [Int])) (fromList (ys :: [Int])))

-- Error case : 0 [1073741824,0]
-- QuickCheck 2.1 finds this easily. 
-- The above error case hit the limit of Int. 
-- Maybe I should use Integer after all?
prop_closest n xs =
  -- Some arbitrary level so that we don't hit the limit of Int
  all (\x -> abs x < 100000) xs ==>
  case (closest n (fromList xs),xs) of
    (Nothing,[]) -> True
    (Just (_,d),ys) -> d == minimum (map (distance n) (ys::[Int]))
    _ -> False

-- Testing the relations between operations

prop_insertDelete n xs =
  trans (delete n . insert n) xs == L.sort (xs::[Int])

prop_sizeEmpty = size empty == 0

prop_sizeFromList xs = size (fromList xs) == length (xs :: [Int])

prop_sizeSucc n xs = size (insert (n::Int) tree) == size tree + 1
  where tree = fromList xs

prop_sizeDelete n xs 
    = size (delete (n::Int) tree) == 
      size tree - (if n `member` tree then 1 else 0)
  where tree = fromList xs

prop_sizeUnion xs ys = size (union treeXs treeYs) == size treeXs + size treeYs
  where (treeXs,treeYs) = (fromList xs, fromList (ys :: [Int]))

prop_sizeUnions xss = size (unions trees) == sum (map size trees)
  where trees = map fromList (xss :: [[Int]])

prop_unionsMember xss =
    all (\x -> member x tree) (concat (xss :: [[Int]]))
  where tree = unions (map fromList xss)

prop_fromListMember xs =
    all (\x -> member x tree) (xs :: [Int])
  where tree = fromList xs

-- All the tests

data TestCase = forall prop.  Testable prop => Tc String prop

tests = [Tc "empty"              prop_empty
        ,Tc "null"               prop_null
        ,Tc "singleton"          prop_singleton
        ,Tc "fromList"           prop_fromList
        ,Tc "fromList inv"       prop_fromListInv
        ,Tc "insert"             prop_insert
        ,Tc "insert inv"         prop_insertInv
        ,Tc "member"             prop_member
        ,Tc "memberDistance"     prop_memberDistance
        ,Tc "delete"             prop_delete
        ,Tc "delete inv"         prop_deleteInv
        ,Tc "elems"              prop_elems
        ,Tc "elemsDistance"      prop_elemsDistance
        ,Tc "unions"             prop_unions
        ,Tc "unions inv"         prop_unionsInv
        ,Tc "union"              prop_union
        ,Tc "union inv"          prop_unionInv
        ,Tc "closest"            prop_closest
        ,Tc "size/empty"         prop_sizeEmpty
        ,Tc "size/fromList"      prop_sizeFromList
        ,Tc "size/succ"          prop_sizeSucc
        ,Tc "size/delete"        prop_sizeDelete
        ,Tc "size/union"         prop_sizeUnion
        ,Tc "size/unions"        prop_sizeUnions
        ,Tc "insert/delete"      prop_insertDelete
        ,Tc "fromList/member"    prop_fromListMember
        ,Tc "unions/member"      prop_unionsMember
        ,Tc "naiveEmpty"         prop_naiveEmpty
        ,Tc "naiveCons"          prop_naiveCons
        ,Tc "naiveDiff"          prop_naiveDiff
        ]

runTests = mapM_ runTest tests
  where runTest (Tc s prop) 
            = do printf "%-25s :" s
                 result <- quickCheckResult prop
                 case result of
                   Success _   -> return ()
                   GaveUp  _ _ -> return ()
                   _           -> exitFailure
                   
#endif 
