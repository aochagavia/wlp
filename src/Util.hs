module Util where

import qualified Data.Set as Set

-- |Compose with a function with multiple arguments.
-- Equivalent definitions are '(.).(.)' and 'fmap fmap fmap'
(...) :: (a -> b) -> (c -> d -> a) -> (c -> d -> b)
(...) f g x y = f $ g x y