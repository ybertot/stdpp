This file lists "large-ish" changes to the std++ Coq library, but not every
API-breaking change is listed.

## std++ master

- Rename `dom_map_filter` into `dom_map_filter_subseteq` and repurpose
  `dom_map_filter` for the version with the equality. This follows the naming
  convention for similar lemmas.
- Generalize `list_find_Some` and `list_find_None` to become bi-implications.
- Disambiguate Haskell-style notations for partially applied operators. For
  example, change `(!! i)` into `(.!! x)` so that `!!` can also be used as a
  prefix, as done in VST. A sed script to perform the renaming can be found at:
  https://gitlab.mpi-sws.org/iris/stdpp/merge_requests/93
- Add type class `TopSet` for sets with a `⊤` element. Provide instances for
  `boolset`, `propset`, and `coPset`.

## std++ 1.2.1 (released 2019-08-29)

This release of std++ received contributions by Dan Frumin, Michael Sammler,
Paolo G. Giarrusso, Paulo Emílio de Vilhena, Ralf Jung, Robbert Krebbers,
Rodolphe Lepigre, and Simon Spies.

Noteworthy additions and changes:

- Introduce `max` and `min` infix notations for `N` and `Z` like we have for `nat`.
- Make `solve_ndisj` tactic more powerful.
- Add type class `Involutive`.
- Improve `naive_solver` performance in case the goal is trivially solvable.
- Add a bunch of new lemmas for list, set, and map operations.
- Rename `lookup_imap` into `map_lookup_imap`.

## std++ 1.2.0 (released 2019-04-26)

Coq 8.9 is supported by this release, but Coq 8.6 is no longer supported. Use
std++ 1.1 if you have to use Coq 8.6. The repository moved to a new location at
https://gitlab.mpi-sws.org/iris/stdpp and automatically generated Coq-doc of
master is available at https://plv.mpi-sws.org/coqdoc/stdpp/.

This release of std++ received contributions by Dan Frumin, Hai Dang, Jan-Oliver
Kaiser, Mackie Loeffel, Maxime Dénès, Ralf Jung, Robbert Krebbers, and Tej
Chajed.

New features:

- New notations `=@{A}`, `≡@{A}`, `∈@{A}`, `∉@{A}`, `##@{A}`, `⊆@{A}`, `⊂@{A}`,
  `⊑@{A}`, `≡ₚ@{A}` for being explicit about the type.
- A definition of basic telescopes `tele` and some theory about them.
- A simple type class based canceler `NatCancel` for natural numbers.
- A type `binder` for anonymous and named binders to be used in program language
  definitions with string-based binders.
- More results about `set_fold` on sets and multisets.
- Notions of infinite and finite predicates/sets and basic theory about them.
- New operation `map_seq`.
- The symmetric and reflexive/transitive/symmetric closure of a relation (`sc`
  and `rtsc`, respectively).
- Different notions of confluence (diamond property, confluence, local
  confluence) and the relations between these.
- A `size` function for finite maps and prove some properties.
- More results about `Qp` fractions.
- More miscellaneous results about sets, maps, lists, multisets.
- Various type class utilities, e.g. `TCEq`, `TCIf`, `TCDiag`, `TCNoBackTrack`,
  and `tc_to_bool`.
- Generalize `gset_to_propset` to `set_to_propset` for any `SemiSet`.

Changes:

- Consistently use `lia` instead of `omega` everywhere.
- Consistently block `simpl` on all `Z` operations.
- The `Infinite` class is now defined using a function `fresh : list A → A`
  that given a list `xs`, gives an element `fresh xs ∉ xs`.
- Make `default` an abbreviation for `from_option id` (instead of just swapping
  the argument order of `from_option`).
- More efficient `Countable` instance for `list` that is linear instead of
  exponential.
- Improve performance of `set_solver` significantly by introducing specialized
  type class `SetUnfoldElemOf` for propositions involving `∈`.
- Make `gset` a `Definition` instead of a `Notation` to improve performance.
- Use `disj_union` (notation `⊎`) for disjoint union on multisets (that adds the
  multiplicities). Repurpose `∪` on multisets for the actual union (that takes
  the max of the multiplicities). 

Naming:

- Consistently use the `set` prefix instead of the `collection` prefix for
  definitions and lemmas.
- Renaming of classes:
  + `Collection` into `Set_` (`_` since `Set` is a reserved keyword)
  + `SimpleCollection` into `SemiSet`
  + `FinCollection` into `FinSet`
  + `CollectionMonad` into `MonadSet`
- Types:
  + `set A := A → Prop` into `propset`
  + `bset := A → bool` into `boolset`.
- Files:
  + `collections.v` into `sets.v`
  + `fin_collections.v` into `fin_sets.v`
  + `bset` into `boolset`
  + `set` into `propset`
- Consistently use the naming scheme `X_to_Y` for conversion functions, e.g.
  `list_to_map` instead of the former `map_of_list`.

The following `sed` script should perform most of the renaming:

```
sed '
s/SimpleCollection/SemiSet/g;
s/FinCollection/FinSet/g;
s/CollectionMonad/MonadSet/g;
s/Collection/Set\_/g;
s/collection\_simple/set\_semi\_set/g;
s/fin\_collection/fin\_set/g;
s/collection\_monad\_simple/monad\_set\_semi\_set/g;
s/collection\_equiv/set\_equiv/g;
s/\bbset/boolset/g;
s/mkBSet/BoolSet/g;
s/mkSet/PropSet/g;
s/set\_equivalence/set\_equiv\_equivalence/g;
s/collection\_subseteq/set\_subseteq/g;
s/collection\_disjoint/set\_disjoint/g;
s/collection\_fold/set\_fold/g;
s/collection\_map/set\_map/g;
s/collection\_size/set\_size/g;
s/collection\_filter/set\_filter/g;
s/collection\_guard/set\_guard/g;
s/collection\_choose/set\_choose/g;
s/collection\_ind/set\_ind/g;
s/collection\_wf/set\_wf/g;
s/map\_to\_collection/map\_to\_set/g;
s/map\_of\_collection/set\_to\_map/g;
s/map\_of\_list/list\_to\_map/g;
s/map\_of\_to_list/list\_to\_map\_to\_list/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/\bof\_list/list\_to\_set/g;
s/\bof\_option/option\_to\_set/g;
s/elem\_of\_of\_list/elem\_of\_list\_to\_set/g;
s/elem\_of\_of\_option/elem\_of\_option\_to\_set/g;
s/collection\_not\_subset\_inv/set\_not\_subset\_inv/g;
s/seq\_set/set\_seq/g;
s/collections/sets/g;
s/collection/set/g;
s/to\_gmap/gset\_to\_gmap/g;
s/of\_bools/bools\_to\_natset/g;
s/to_bools/natset\_to\_bools/g;
s/coPset\.of_gset/gset\_to\_coPset/g;
s/coPset\.elem\_of\_of\_gset/elem\_of\_gset\_to\_coPset/g;
s/of\_gset\_finite/gset\_to\_coPset\_finite/g;
s/set\_seq\_S\_disjoint/set\_seq\_S\_end\_disjoint/g;
s/set\_seq\_S\_union/set\_seq\_S\_end\_union/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/of\_bools/bools\_to\_natset/g;
s/to\_bools/natset\_to\_bools/g;
' -i $(find -name "*.v")
```

## std++ 1.1.0 (released 2017-12-19)

Coq 8.5 is no longer supported by this release of std++.  Use std++ 1.0 if you
have to use Coq 8.5.

New features:

- Many new lemmas about lists, vectors, sets, maps.
- Equivalence proofs between std++ functions and their alternative in the the
  Coq standard library, e.g. `List.nth`, `List.NoDop`.
- Typeclass versions of the logical connectives and list predicates:
  `TCOr`, `TCAnd`, `TCTrue`, `TCForall`, `TCForall2`.
- A function `tc_opaque` to make definitions type class opaque.
- A type class `Infinite` for infinite types.
- A generic implementation to obtain fresh elements of infinite types.
- More theory about curry and uncurry functions on `gmap`.
- A generic `filter` and `zip_with` operation on finite maps.
- A type of generic trees for showing that arbitrary types are countable.

Changes:

- Get rid of `Automatic Coercions Import`, it is deprecated.
  Also get rid of `Set Asymmetric Patterns`.
- Various changes and improvements to `f_equiv` and `solve_proper`.
- `Hint Mode` is now set for all operational type classes to make instance
  search less likely to diverge.
- New type class `RelDecision` for decidable relations, and `EqDecision` is
  defined in terms of it. This class allows to set `Hint Mode` properly.
- Use the flag `assert` of `Arguments` to make it more robust.
- The functions `imap` and `imap2` on lists are defined so that they enjoy more
  definitional equalities.
- Theory about `fin` is moved to its own file `fin.v`.
- Rename `preserving` → `mono`.

Changes to notations:

- Operational type classes for lattice notations: `⊑`,`⊓`, `⊔`, `⊤` `⊥`.
- Replace `⊥` for disjointness with `##`, so that `⊥` can be used for the
  bottom lattice element.
- All notations are now in `stdpp_scope` with scope key `stdpp`
  (formerly `C_scope` and `C`).
- Higher precedence for `.1` and `.2` that is compatible with ssreflect.
- Various changes to monadic notations to improve compatibility with Mtac2:
  + Pattern matching notation for monadic bind `'pat ← x; y` where `pat` can
    be any Coq pattern.
  + Change the level of the do-notation.
  + `<$>` is left associative.
  + Notation `x ;; y` for `_ ← x; y`.

## History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.
