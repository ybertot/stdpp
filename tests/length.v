(** Check that we always get the [length] function on lists, not on strings. *)
From stdpp Require Import prelude.
Check length.
From stdpp Require Import strings.
Check length.
From stdpp Require Import prelude.
Check length.