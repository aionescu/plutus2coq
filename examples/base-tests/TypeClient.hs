module TypeClient where

-- Can't refer to modules named Type
-- Should rename the module
import Type

g :: Int
g = Type.id 3
