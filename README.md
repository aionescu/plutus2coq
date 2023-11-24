# plutus2coq

This project aims to enable Plutus smart contract development in Coq, by providing Coq translations of PlutusTx and associated libraries, using `hs-to-coq`.

## Repository contents

* [hs-to-coq](hs-to-coq) and [plutus](plutus): Git subtrees containing the source code of the 2 projects
* [scripts](scripts): The main scripts used to translate to Coq and compile the generated code
* [edits](edits): Coq preamble and edit files used by hs-to-coq while translating
* [plutus-coq](plutus-coq): The generated PlutusTx Coq files
* [examples/math-bounty](examples/math-bounty): An example smart contract written in Coq using the translated libraries, and extracted back to Haskell. More info can be found in the README inside its directory.

## Re-generating the Coq files

The generated Coq artifacts are included in the [plutus-coq](plutus-coq) directory, and the project can be used without re-generating them. If you still wish to re-generate them (e.g. with a newer Plutus version), the requirements and instructions are described below:

### Required tools & libraries

* libsodium & libblst
* GHC 8.10.7
* Stack 2.11.1
* Coq 8.10.2 and packages coq-ssreflect 1.10.0, coq-itree 3.0.0

### System packages

Plutus depends on the `libsodium` and `libblst` libraries.

On Arch-based Linux distributions, they can be installed through pacman: `sudo pacman -S libsodium libblst`.

On Debian-based distros, only `libsodium` is available via `apt`, and `libblst` has to be built from [source](https://github.com/supranational/blst).

### GHC & Stack

It's recommended to install GHC and Stack via [GHCup](https://www.haskell.org/ghcup/):

```bash
ghcup install ghc --set 8.10.7
ghcup install stack --set 2.11.1
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

### Coq & Coq packages

To install Coq 8.10.2 and related packages, it's recommended to use [OPAM](https://opam.ocaml.org/doc/Install.html):

```bash
opam switch create plutus2coq 4.09.1
eval $(opam env --switch=plutus2coq)
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

## Generating the Coq files

To translate the Plutus libraries to Coq, simply run the [scripts/translate.sh](scripts/translate.sh) script.

Afterwards, run the [scripts/compile.sh](scripts/compile.sh) script to compile the Coq files.

```bash
./scripts/translate.sh
./scripts/compile.sh
```

The generated files are written to the [plutus-coq](plutus-coq) directory.
