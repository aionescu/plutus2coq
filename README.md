# plutus2coq

Translating the Plutus standard library to Coq

## Installing prerequisites

* GHC 8.10.7
* Stack 2.11.1
* Coq 8.10.2 + coq-ssreflect 1.10.0 + coq-itree 3.0.0

It's recommended to install GHC and Stack via [GHCup](https://www.haskell.org/ghcup/):

```bash
ghcup install ghc 8.10.7
ghcup install stack 2.11.1
```

It's also recommended to configure Stack to resolve GHC versions through GHCup, using [hooks](https://www.haskell.org/ghcup/guide/#strategy-2-stack-hooks-new-recommended):

```bash
mkdir -p ~/.stack/hooks/
curl https://raw.githubusercontent.com/haskell/ghcup-hs/master/scripts/hooks/stack/ghc-install.sh > ~/.stack/hooks/ghc-install.sh
chmod +x ~/.stack/hooks/ghc-install.sh
stack config set system-ghc false --global
```

Since Stack 2.11.1 is not the newest version, Stack will warn you to upgrade every time it is run. This can be safely ignored by adding the following line to your Stack config:

```bash
echo "recommend-stack-upgrade: false" >>~/.stack/config.yaml
```

To install Coq 8.10.2 and related packages, it's recommended to use [OPAM](https://opam.ocaml.org/doc/Install.html):

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.10.2 coq-mathcomp-ssreflect.1.10.0 coq-itree.3.0.0
```

## Setting up `hs-to-coq`

There is a one-time setup that must be performed for `hs-to-coq`. The first step is to build it using Stack:

```bash
cd hs-to-coq
stack build
```

Then, build the Coq translations for Haskell's `base` library:

```bash
cd base     && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..
cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..
```

You might get some Coq warnings, which are safe to ignore.

Once done, change back to the repo's root directory:

```bash
cd ..
```

## Running the project

The translation process is split into three steps:

```bash
./scripts/translate.sh # Translate the Plutus files to Coq using hs-to-coq
./scripts/compile.sh   # Compile the generated Coq code
./scripts/extract.sh   # Extract the generated Coq code to Haskell
```

The final output is a Cabal project containing the extracted Haskell code, in the `coq-extracted` directory:

```shell
cd coq-extracted
cabal build
```
