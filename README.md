# plutus2coq

Translating the Plutus standard library to Coq

## Installing prerequisites

* GHC 8.10.7
* Stack 2.11.1
* Coq 8.10.2 + ssreflect 1.10.0 + itree 3.0.0

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

## Building the project

The first step of building the project is to build `hs-to-coq`:

```bash
cd hs-to-coq
stack build
```

Then, you should build the Coq translations for Haskell's `base` library:

```bash
cd base && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..
cd base-thy && coq_makefile -f _CoqProject -o Makefile && make -j && cd ..
```

You might get some Coq warnings, which are safe to ignore.

Once done, don't forget to change back to the repo's root directory:

```bash
cd ..
```

Finally, you can run the main script, `convert.sh`, to translate the Plutus standard library to Coq:

```bash
./scripts/convert.sh
```

You will find the output in the `coq-output` directory.
