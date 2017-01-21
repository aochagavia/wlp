module Util where

import qualified Data.Set as Set

-- |Compose with a function with multiple arguments.
-- Equivalent definitions are '(.).(.)' and 'fmap fmap fmap'
(...) :: (a -> b) -> (c -> d -> a) -> (c -> d -> b)
(...) f g x y = f $ g x y

-- |Convert an 'Either' to its 'Right' value.
-- Throws an error when this is not possible.
-- You might want to use this to cover programmer errors.
fromRight :: Show l => Either l r -> r
fromRight (Left err) = error $ "Unexpected error " ++ show err
fromRight (Right a) = a
