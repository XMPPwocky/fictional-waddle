# Lean proofs

Lean 4 files built against Mathlib (version pinned in `lake-manifest.json`). Every file compiles with no `sorry`
and no added axioms; `#print axioms` shows only Lean's standard three (propext, Classical.choice, Quot.sound),
and some theorems use none. `MANIFEST.tsv` lists every file with its count of theorems and lemmas.

## Reading the files

Each file opens with a docstring that separates:

- **PROVED**: what the Lean statements say. Judge a file by this section.
- **INTERPRETED** or **CITED**: readings and outside results that are not formalized in the file.

Most of the mathematics is known; the files state it exactly and check it. Some file names are playful and
come from the ideas that prompted them.

## Known limitation

Lean guarantees that each proof is correct for its statement. It cannot guarantee that a statement means what
its title or docstring says. The statements have not yet been reviewed by a human against their intended
meaning. A good check: pick files at random, write down what each statement should say from its docstring,
then compare with the Lean.

## Building

Put `lakefile.toml`, `lean-toolchain` and `lake-manifest.json` in an empty directory with the `scratch/` and
`BoundaryTheorem/` folders and `BoundaryTheorem.lean`, run `lake exe cache get`, then `lake env lean <file>`.
