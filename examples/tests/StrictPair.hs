
module StrictPair (StrictPair(..), toPair) where

-- | The same as a regular Haskell pair, but
--
-- @
-- (x :*: _|_) = (_|_ :*: y) = _|_
-- @
data StrictPair a b = !a :*: !b

infixr 1 :*:

-- | Convert a strict pair to a standard pair.
toPair :: StrictPair a b -> (a, b)
toPair (x :*: y) = (x, y)
{-# INLINE toPair #-}

fromPair :: (a,b) -> StrictPair a b
fromPair (x, y) = (x :*: y)
{-# INLINE fromPair #-}
