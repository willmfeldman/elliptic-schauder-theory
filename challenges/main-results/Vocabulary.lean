/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Vocabulary.HalfSpace
public import Vocabulary.Holder
public import Vocabulary.Elliptic
public import Vocabulary.Div
public import Vocabulary.Nondiv

/-!
# Vocabulary: the headline theorems (divergence and nondivergence form)

Challenge vocabulary: a Mathlib-only restatement, one module per library file, in this order,
of the library files

* `BasicElliptic/Basic/HalfSpace.lean`
* `BasicElliptic/Defs/Holder.lean`
* `BasicElliptic/Defs/Elliptic.lean`
* `BasicElliptic/Defs/Div.lean`
* `BasicElliptic/Defs/Nondiv.lean`

Each part keeps the library's names, definitions and order, with the theorems dropped, and
keeps its `open` commands inside its own section. The vocabulary is split along the library's module
boundaries (`Vocabulary/*.lean`) and `Challenge.lean` imports those modules directly, because Lean
names auxiliary proofs per module and a concatenated restatement would not match the library's
values; Comparator checks each copied declaration
against the library by name and value.
-/

@[expose] public section
