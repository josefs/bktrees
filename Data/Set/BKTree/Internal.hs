{- | 
   Module      : Data.Set.BKTree.Internal
   Copyright   : (c) Josef Svenningsson 2010
   License     : BSD-style
   Maintainer  : josef.svenningsson@gmail.com
   Stability   : Alpha quality. Interface may change without notice.
   Portability : portable

   This module exposes the internal representation of Burkhard-Keller trees.
-}
module Data.Set.BKTree.Internal where

import Data.IntMap

-- | The type of Burkhard-Keller trees.
data BKTree a = Node a !Int (IntMap (BKTree a))
              | Empty
#ifdef DEBUG
                deriving Show
#endif
