# Iris-Logatom

This Rocq development collects useful theorems about the Iris logically
atomic triple, including the soundness and completeness of it with respect
to linearizability, and several techniques to establish logical atomicity.

## Building the development

This development is known to compile with

- [Rocq](https://rocq-prover.org/) 9.1.0
- [std++](https://gitlab.mpi-sws.org/iris/stdpp) 1.13.0
- [Iris](https://gitlab.mpi-sws.org/iris/iris/) 4.5.0
- [Autosubst](https://github.com/rocq-community/autosubst) dev

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install opam if not already installed.
2. Create a new switch and link it to the repository.
```sh
opam switch create iris-logatom 5.4.0
opam switch link iris-logatom .
```
3. Add the Rocq and Iris opam repositories.
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install dependencies as specified in the opam file.
```sh
opam install . --deps-only
```
5. Build the development.
```sh
eval $(opam env)
make
```
6. (Optional) Print axioms used by end-to-end specifications.
```sh
python3 print_axioms.py
```

## Code structure

The main results are in the `theories/` directory, and end-to-end
specifications for queue algorithms are in the `case_studies/` directory.

- `theories/pure_logic/linear.v`: the formal definition of linearizability.
- `theories/program_logic/atomic_complete.v`: the completeness theorem of
  logical atomicity.
- `theories/program_logic/atomic_sound.v`: the reformulation of
  Birkedal et al.'s soundness theorem of logical atomicity.
- `theories/heap_lang/mgc.v`: the construction of the most general client and
  the reformulation of Birkedal et al.'s Iris specification to trace invariant
  theorem.
-  `theories/heap_lang/refines_linearizable.v`: the theorem that refinement
  transports logical atomicity.
- `theories/pure_logic/aspect/`: the reformulation of the aspect-oriented
  proof technique by Henzinger et al.
- `theoires/pure_logic/refine/`: the reformulation of the forward simulation
  technique by Bouajjani et al.
- `theoires/pure_logic/metaconfig/`: the reformulation of the
  meta-configuration tracking technique by Jayanti et al.

## Axioms

The verification of Herlihy-Wing queue using meta-configuration tracking
depends on extensionality axioms.

```rocq
FunctionalExtensionality.functional_extensionality_dep : ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x), (∀ x : A, f x = g x) → f = g
PropExtensionality.propositional_extensionality : ∀ P Q : Prop, P ↔ Q → P = Q
```

## License

This repository is licensed under the BSD 2-Clause “Simplified” License.
