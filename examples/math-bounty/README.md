# examples/math-bounty

This directory contains a simple Math Bounty smart contract, written in Coq using the translated Plutus libraries, and extracted back to Haskell.

The most interesting file is the contract script itself, [MathBounty.v](src-coq/MathBounty.v), which contains the `mathBounty` validator definition, as well as a proof of correctness.

The [compile.sh](compile.sh) script can be used to compile the contract and extract it to Haskell, generating [MathBounty.hs](src-hs/MathBounty.hs). However, this extracted file needs some manual adjustments to be compilable by Plutus. The fixed file is available as [MathBountyFixed.hs](src-hs/MathBountyFixed.hs).

Finally, this fixed-up module can be compiled by running `cabal build math-bounty`, using the wrapper Cabal module defined in [math-bounty.cabal](math-bounty.cabal).

Note: The Cabal project doesn't actually compile, as the PlutusTx Plugin (which is required to compile Haskell to Plutus Core) only compiles with GHC 9.2 and above, and this project uses GHC 8.10.7 (this is the latest version supported by `hs-to-coq`).
