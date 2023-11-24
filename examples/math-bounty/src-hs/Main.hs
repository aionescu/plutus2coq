module Main where


import Data.ByteString qualified as B
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Short qualified as B
import PlutusLedgerApi.V2 qualified as V2

import MathBountyFixed

main :: IO ()
main =
  B.writeFile "MathBounty.uplc" $ Base16.encode $ B.fromShort $ V2.serialiseCompiledCode mathBountyValidatorScript
