# examples/math-bounty

This directory contains a simple Math Bounty smart contract, written in Coq using the translated Plutus libraries, and extracted back to Haskell.

The most interesting file is the contract script itself, [MathBounty.v](src-coq/MathBounty.v), which contains the `mathBounty` validator definition, as well as a proof of correctness.

The [extract.sh](extract.sh) script can be used to compile the contract and extract it to Haskell, generating [MathBounty.hs](src-hs/MathBounty.hs). (Before this step, make sure the translated Plutus Coq files are compiled by running `./scripts/compile.sh`)

However, this extracted file needs some manual adjustments to be compilable by Plutus. The fixed-up version is available as [MathBountyFixed.hs](src-hs/MathBountyFixed.hs).

Finally, this fixed-up module can be compiled by running `cabal build --with-compiler=ghc-9.2 math-bounty`, using the wrapper Cabal project defined in [math-bounty.cabal](math-bounty.cabal).

Note: It's required to compile the Cabal project with GHC >=9.2, as the PlutusTx Plugin (which is required to compile Haskell to Plutus Core) requires GHC >=9.2.
