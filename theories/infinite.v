(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import pretty fin_collections.

(** The class [Infinite] axiomatizes types with infinitely many elements
by giving an injection from the natural numbers into the type. It is mostly
used to provide a generic [fresh] algorithm. *)
Class Infinite A :=
  { inject: nat → A;
    inject_injective:> Inj (=) (=) inject }.

Instance string_infinite: Infinite string := {| inject := λ x, "~" +:+ pretty x |}.
Instance nat_infinite: Infinite nat := {| inject := id |}.
Instance N_infinite: Infinite N := {| inject_injective := Nat2N.inj |}.
Instance pos_infinite: Infinite positive := {| inject_injective := SuccNat2Pos.inj |}.
Instance Z_infinite: Infinite Z := {| inject_injective := Nat2Z.inj |}.
Instance option_infinite `{Infinite A}: Infinite (option A) := {| inject := Some ∘ inject |}.
Program Instance list_infinite `{Inhabited A}: Infinite (list A) :=
  {| inject := λ i, replicate i inhabitant |}.
Next Obligation.
Proof.
  intros * i j eqrep%(f_equal length).
  rewrite !replicate_length in eqrep; done.
Qed.

(** Derive fresh instances. *)
Section StringFresh.
  Context `{FinCollection string C, ∀ (x: string) (s: C), Decision (x ∈ s)}.
  Global Instance string_fresh: Fresh string C := fresh_generic.
  Global Instance string_fresh_spec: FreshSpec string C := _.
End StringFresh.
