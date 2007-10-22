{- | 
   Module      : Data.Set.BKTree
   Copyright   : (c) Josef Svenningsson 2007
   License     : BSD-style
   Maintainer  : josef.svenningsson@gmail.com
   Stability   : Alpha quality. Interface may change without notice.
   Portability : portable

   Burhard-Keller trees provide an implementation of sets which apart
   from the ordinary operations also has an approximate member search,
   allowing you to search for elements that are of a distance @n@ from
   the element you are searching for. The distance is determined using
   a metric on the type of elements. Therefore all elements must
   implement the 'Metric' type class, rather than the more usual
   'Ord'.

   Useful metrics include the manhattan distance between two points,
   the Levenshtein edit distance between two strings, the number of
   edges in the shortest path between two nodes in a undirected graph
   and the Hamming distance between two binary strings. Any euclidean
   space also has a metric. However, in this module we use int-valued
   metrics and that doesn't quite with the metrics of euclidean spaces
   which are real-values.

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
--    ,Manhattan(..)
     --
    ,null,empty
    ,fromList
    ,insert
    ,member,memberDistance
    ,delete
    ,union,unions
    ,elems,elemsDistance
    ,closest
    )where

import qualified Data.IntMap as M
import qualified Data.List as L hiding (null)
import Prelude hiding (null)
#ifdef DEBUG
import Test.QuickCheck
#endif
data BKTree a = Node a (M.IntMap (BKTree a))
              | Empty
#ifdef DEBUG
                deriving Show
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

-- | Test if the tree is empty.
null :: BKTree a -> Bool
null (Empty)    = True
null (Node _ _) = False

-- | The empty tree.
empty :: BKTree a
empty = Empty

-- | Inserts an element into the tree. If an element is inserted several times
--   it will be stored several times.
insert :: Metric a => a -> BKTree a -> BKTree a
insert a Empty = Node a M.empty
insert a (Node b map) = Node b map'
  where map' = M.insertWith recurse d Empty map
        d    = distance a b
        recurse _ tree = insert a tree

-- | Checks whether an element is in the tree.
member :: Metric a => a -> BKTree a -> Bool
member a Empty = False
member a (Node b map) 
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
memberDistance n a (Node b map)
    | d <= n    = True
    | otherwise = any (memberDistance n a) (M.elems subMap)
    where d = distance a b
          subMap = case M.split (d-n-1) map of
                     (_,mapRight) ->                         
                         case M.split (d+n+1) mapRight of
                          (mapCenter,_) -> mapCenter

-- | Removes an element from the tree. If an element occurs several times in 
--   the only the first occurrence will be deleted.
delete :: Metric a => a -> BKTree a -> BKTree a
delete a Empty = Empty
delete a t@(Node b map) 
    | d == 0    = unions (M.elems map)
    | otherwise = Node b (M.update (Just . delete a) d map)
    where d = distance a b

-- | Returns all the elements of the tree
elems :: BKTree a -> [a]
elems Empty = []
elems (Node a imap) = a : concatMap elems (M.elems imap)


-- | @'elemsDistance' n a tree@ returns all the elements in @tree@ which are 
--   at a 'distance' less than or equal to @n@ from the element @a@.
elemsDistance :: Metric a => Int -> a -> BKTree a -> [a]
elemsDistance n a Empty = []
elemsDistance n a (Node b imap) 
    = (if d <= n then (b :) else id) $
      concatMap (elemsDistance n a) (M.elems subMap)
    where d = distance a b
          subMap = case M.split (d-n-1) imap of
                     (_,mapRight) -> 
                         case M.split (d+n+1) mapRight of
                           (mapCenter,_) -> mapCenter

-- | Constructs a tree from a list
fromList :: Metric a => [a] -> BKTree a
fromList []     = Empty
fromList (a:as) = Node a $
                  M.fromAscList $
                  map recurse $
                  L.groupBy ((==) `on` fst) $
                  L.sortBy (compare `on` fst) $
                  map mkDistance $
                  as
  where mkDistance b = (distance a b,b)
        recurse bs@((k,_):_) = (k,fromList (map snd bs))

-- | Merges several trees
unions :: Metric a => [BKTree a] -> BKTree a
unions []  = Empty
unions (Empty:ts) = unions ts
unions (Node piv pmap:ts) = Node piv $
                            M.fromAscList $
                            map recurse $
                            L.groupBy ((==) `on` fst) $
                            L.sortBy (compare `on` fst) $
                            (M.toList pmap ++) $
                            concatMap mkDistance $
                            ts
    where mkDistance n@(Node a _) = [(distance piv a,n)]
          mkDistance _            = []
          recurse    bs@((k,_):_) = (k,unions (map snd bs))

-- | Merges two trees
union :: Metric a => BKTree a -> BKTree a -> BKTree a
union t1 t2 = unions [t1,t2]

-- | @'closest' a tree@ returns the element in @tree@ which is closest to
--   @a@ together with the distance. Returns @Nothing@ if the tree is empty.
closest :: Metric a => a -> BKTree a -> Maybe (a,Int)
closest a Empty = Nothing
closest a tree@(Node b _) = Just (closeLoop a (b,distance a b) tree)

closeLoop a candidate Empty     = candidate
closeLoop a candidate@(b,d) (Node x imap)
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

prop_empty n = not (member (n::Int) empty)

prop_insert n xs = error "Unimplemented"

prop_member n xs = member n (fromList xs) == L.elem (n::Int) xs

prop_memberDistance dist n xs = 
 let d   = dist `mod` 5
     ref = L.any (\e -> distance n e <= d) xs
 in collect ref $
 memberDistance d n (fromList xs) == 
 L.any (\e -> distance n e <= d) (xs :: [Int])

prop_delete n xs =
  L.sort (elems (delete n (fromList xs))) == 
  L.sort (removeFirst (xs :: [Int]))
 where removeFirst [] = []
       removeFirst (a:as) | a == n    = as
                          | otherwise = a : removeFirst as

prop_elems xs = L.sort (elems (fromList xs)) == L.sort (xs::[Int])

prop_elemsDistance d n xs = 
  L.sort (elemsDistance d n (fromList xs)) == 
  L.sort (filter (\e -> distance n e <= d) xs)

prop_unions xss = 
    L.sort (elems (unions (map fromList xss))) == 
    L.sort (concat (xss::[[Int]]))

prop_union xs ys =
    L.sort (elems (union (fromList xs) (fromList ys))) ==
    L.sort (xs ++ (ys::[Int]))

prop_closest n xs =
  case (closest n (fromList xs),xs) of
    (Nothing,[]) -> True
    (Just (_,d),ys) -> d == minimum (map (distance n) (ys::[Int]))
    _ -> False

#endif 
