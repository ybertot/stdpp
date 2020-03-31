From stdpp Require Import gmap.
Set Default Proof Using "Type".

Record gmultiset A `{Countable A} := GMultiSet { gmultiset_car : gmap A nat }.
Arguments GMultiSet {_ _ _} _ : assert.
Arguments gmultiset_car {_ _ _} _ : assert.

Instance gmultiset_eq_dec `{Countable A} : EqDecision (gmultiset A).
Proof. solve_decision. Defined.

Program Instance gmultiset_countable `{Countable A} :
    Countable (gmultiset A) := {|
  encode X := encode (gmultiset_car X); decode p := GMultiSet <$> decode p
|}.
Next Obligation. intros A ?? [X]; simpl. by rewrite decode_encode. Qed.

Section definitions.
  Context `{Countable A}.

  Definition multiplicity (x : A) (X : gmultiset A) : nat :=
    match gmultiset_car X !! x with Some n => S n | None => 0 end.
  Global Instance gmultiset_elem_of : ElemOf A (gmultiset A) := λ x X,
    0 < multiplicity x X.
  Global Instance gmultiset_subseteq : SubsetEq (gmultiset A) := λ X Y, ∀ x,
    multiplicity x X ≤ multiplicity x Y.
  Global Instance gmultiset_equiv : Equiv (gmultiset A) := λ X Y, ∀ x,
    multiplicity x X = multiplicity x Y.

  Global Instance gmultiset_elements : Elements A (gmultiset A) := λ X,
    let (X) := X in ''(x,n) ← map_to_list X; replicate (S n) x.
  Global Instance gmultiset_size : Size (gmultiset A) := length ∘ elements.

  Global Instance gmultiset_empty : Empty (gmultiset A) := GMultiSet ∅.
  Global Instance gmultiset_singleton : Singleton A (gmultiset A) := λ x,
    GMultiSet {[ x := 0 ]}.
  Global Instance gmultiset_union : Union (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ union_with (λ x y, Some (x `max` y)) X Y.
  Global Instance gmultiset_intersection : Intersection (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ intersection_with (λ x y, Some (x `min` y)) X Y.
  (** Often called the "sum" *)
  Global Instance gmultiset_disj_union : DisjUnion (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ union_with (λ x y, Some (S (x + y))) X Y.
  Global Instance gmultiset_difference : Difference (gmultiset A) := λ X Y,
    let (X) := X in let (Y) := Y in
    GMultiSet $ difference_with (λ x y,
      let z := x - y in guard (0 < z); Some (pred z)) X Y.

  Global Instance gmultiset_dom : Dom (gmultiset A) (gset A) := λ X,
    let (X) := X in dom _ X.
End definitions.

Typeclasses Opaque gmultiset_elem_of gmultiset_subseteq.
Typeclasses Opaque gmultiset_elements gmultiset_size gmultiset_empty.
Typeclasses Opaque gmultiset_singleton gmultiset_union gmultiset_difference.
Typeclasses Opaque gmultiset_dom.

Section lemmas.
Context `{Countable A}.
Implicit Types x y : A.
Implicit Types X Y : gmultiset A.

Lemma gmultiset_eq X Y : X = Y ↔ ∀ x, multiplicity x X = multiplicity x Y.
Proof.
  split; [by intros ->|intros HXY].
  destruct X as [X], Y as [Y]; f_equal; apply map_eq; intros x.
  specialize (HXY x); unfold multiplicity in *; simpl in *.
  repeat case_match; naive_solver.
Qed.
Global Instance gmultiset_leibniz : LeibnizEquiv (gmultiset A).
Proof. intros X Y. by rewrite gmultiset_eq. Qed.
Global Instance gmultiset_equiv_equivalence : Equivalence (≡@{gmultiset A}).
Proof. constructor; repeat intro; naive_solver. Qed.

(* Multiplicity *)
Lemma multiplicity_empty x : multiplicity x ∅ = 0.
Proof. done. Qed.
Lemma multiplicity_singleton x : multiplicity x {[ x ]} = 1.
Proof. unfold multiplicity; simpl. by rewrite lookup_singleton. Qed.
Lemma multiplicity_singleton_ne x y : x ≠ y → multiplicity x {[ y ]} = 0.
Proof. intros. unfold multiplicity; simpl. by rewrite lookup_singleton_ne. Qed.
Lemma multiplicity_singleton' x y :
  multiplicity x {[ y ]} = if decide (x = y) then 1 else 0.
Proof.
  destruct (decide _) as [->|].
  - by rewrite multiplicity_singleton.
  - by rewrite multiplicity_singleton_ne.
Qed.
Lemma multiplicity_union X Y x :
  multiplicity x (X ∪ Y) = multiplicity x X `max` multiplicity x Y.
Proof.
  destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
  rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; lia.
Qed.
Lemma multiplicity_intersection X Y x :
  multiplicity x (X ∩ Y) = multiplicity x X `min` multiplicity x Y.
Proof.
  destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
  rewrite lookup_intersection_with. destruct (X !! _), (Y !! _); simpl; lia.
Qed.
Lemma multiplicity_disj_union X Y x :
  multiplicity x (X ⊎ Y) = multiplicity x X + multiplicity x Y.
Proof.
  destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
  rewrite lookup_union_with. destruct (X !! _), (Y !! _); simpl; lia.
Qed.
Lemma multiplicity_difference X Y x :
  multiplicity x (X ∖ Y) = multiplicity x X - multiplicity x Y.
Proof.
  destruct X as [X], Y as [Y]; unfold multiplicity; simpl.
  rewrite lookup_difference_with.
  destruct (X !! _), (Y !! _); simplify_option_eq; lia.
Qed.

(* Set_ *)
Lemma elem_of_multiplicity x X : x ∈ X ↔ 0 < multiplicity x X.
Proof. done. Qed.

Global Instance gmultiset_simple_set : SemiSet A (gmultiset A).
Proof.
  split.
  - intros x. rewrite elem_of_multiplicity, multiplicity_empty. lia.
  - intros x y.
    rewrite elem_of_multiplicity, multiplicity_singleton'.
    destruct (decide (x = y)); intuition lia.
  - intros X Y x. rewrite !elem_of_multiplicity, multiplicity_union. lia.
Qed.
Global Instance gmultiset_elem_of_dec : RelDecision (∈@{gmultiset A}).
Proof. refine (λ x X, cast_if (decide (0 < multiplicity x X))); done. Defined.

Lemma gmultiset_elem_of_disj_union X Y x : x ∈ X ⊎ Y ↔ x ∈ X ∨ x ∈ Y.
Proof. rewrite !elem_of_multiplicity, multiplicity_disj_union. lia. Qed.

Global Instance set_unfold_gmultiset_disj_union x X Y P Q :
  SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
  SetUnfoldElemOf x (X ⊎ Y) (P ∨ Q).
Proof.
  intros ??; constructor. rewrite gmultiset_elem_of_disj_union.
  by rewrite <-(set_unfold_elem_of x X P), <-(set_unfold_elem_of x Y Q).
Qed.

(* Algebraic laws *)
(** For union *)
Global Instance gmultiset_union_comm : Comm (=@{gmultiset A}) (∪).
Proof.
  intros X Y. apply gmultiset_eq; intros x. rewrite !multiplicity_union; lia.
Qed.
Global Instance gmultiset_union_assoc : Assoc (=@{gmultiset A}) (∪).
Proof.
  intros X Y Z. apply gmultiset_eq; intros x. rewrite !multiplicity_union; lia.
Qed.
Global Instance gmultiset_union_left_id : LeftId (=@{gmultiset A}) ∅ (∪).
Proof.
  intros X. apply gmultiset_eq; intros x.
  by rewrite multiplicity_union, multiplicity_empty.
Qed.
Global Instance gmultiset_union_right_id : RightId (=@{gmultiset A}) ∅ (∪).
Proof. intros X. by rewrite (comm_L (∪)), (left_id_L _ _). Qed.
Global Instance gmultiset_union_idemp : IdemP (=@{gmultiset A}) (∪).
Proof.
  intros X. apply gmultiset_eq; intros x. rewrite !multiplicity_union; lia.
Qed.

(** For intersection *)
Global Instance gmultiset_intersection_comm : Comm (=@{gmultiset A}) (∩).
Proof.
  intros X Y. apply gmultiset_eq; intros x. rewrite !multiplicity_intersection; lia.
Qed.
Global Instance gmultiset_intersection_assoc : Assoc (=@{gmultiset A}) (∩).
Proof.
  intros X Y Z. apply gmultiset_eq; intros x. rewrite !multiplicity_intersection; lia.
Qed.
Global Instance gmultiset_intersection_left_absorb : LeftAbsorb (=@{gmultiset A}) ∅ (∩).
Proof.
  intros X. apply gmultiset_eq; intros x.
  by rewrite multiplicity_intersection, multiplicity_empty.
Qed.
Global Instance gmultiset_intersection_right_absorb : RightAbsorb (=@{gmultiset A}) ∅ (∩).
Proof. intros X. by rewrite (comm_L (∩)), (left_absorb_L _ _). Qed.
Global Instance gmultiset_intersection_idemp : IdemP (=@{gmultiset A}) (∩).
Proof.
  intros X. apply gmultiset_eq; intros x. rewrite !multiplicity_intersection; lia.
Qed.

Lemma gmultiset_union_intersection_l X Y Z : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).
Proof.
  apply gmultiset_eq; intros y.
  rewrite multiplicity_union, !multiplicity_intersection, !multiplicity_union. lia.
Qed.
Lemma gmultiset_union_intersection_r X Y Z : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z).
Proof. by rewrite <-!(comm_L _ Z), gmultiset_union_intersection_l. Qed.
Lemma gmultiset_intersection_union_l X Y Z : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).
Proof.
  apply gmultiset_eq; intros y.
  rewrite multiplicity_union, !multiplicity_intersection, !multiplicity_union. lia.
Qed.
Lemma gmultiset_intersection_union_r X Y Z : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z).
Proof. by rewrite <-!(comm_L _ Z), gmultiset_intersection_union_l. Qed.

(** For disjoint union (aka sum) *)
Global Instance gmultiset_disj_union_comm : Comm (=@{gmultiset A}) (⊎).
Proof.
  intros X Y. apply gmultiset_eq; intros x. rewrite !multiplicity_disj_union; lia.
Qed.
Global Instance gmultiset_disj_union_assoc : Assoc (=@{gmultiset A}) (⊎).
Proof.
  intros X Y Z. apply gmultiset_eq; intros x. rewrite !multiplicity_disj_union; lia.
Qed.
Global Instance gmultiset_disj_union_left_id : LeftId (=@{gmultiset A}) ∅ (⊎).
Proof.
  intros X. apply gmultiset_eq; intros x.
  by rewrite multiplicity_disj_union, multiplicity_empty.
Qed.
Global Instance gmultiset_disj_union_right_id : RightId (=@{gmultiset A}) ∅ (⊎).
Proof. intros X. by rewrite (comm_L (⊎)), (left_id_L _ _). Qed.

Global Instance gmultiset_disj_union_inj_1 X : Inj (=) (=) (X ⊎.).
Proof.
  intros Y1 Y2. rewrite !gmultiset_eq. intros HX x; generalize (HX x).
  rewrite !multiplicity_disj_union. lia.
Qed.
Global Instance gmultiset_disj_union_inj_2 X : Inj (=) (=) (.⊎ X).
Proof. intros Y1 Y2. rewrite <-!(comm_L _ X). apply (inj _). Qed.

Lemma gmultiset_disj_union_intersection_l X Y Z : X ⊎ (Y ∩ Z) = (X ⊎ Y) ∩ (X ⊎ Z).
Proof.
  apply gmultiset_eq; intros y.
  rewrite multiplicity_disj_union, !multiplicity_intersection,
    !multiplicity_disj_union. lia.
Qed.
Lemma gmultiset_disj_union_intersection_r X Y Z : (X ∩ Y) ⊎ Z = (X ⊎ Z) ∩ (Y ⊎ Z).
Proof. by rewrite <-!(comm_L _ Z), gmultiset_disj_union_intersection_l. Qed.

Lemma gmultiset_disj_union_union_l X Y Z : X ⊎ (Y ∪ Z) = (X ⊎ Y) ∪ (X ⊎ Z).
Proof.
  apply gmultiset_eq; intros y.
  rewrite multiplicity_disj_union, !multiplicity_union,
    !multiplicity_disj_union. lia.
Qed.
Lemma gmultiset_disj_union_union_r X Y Z : (X ∪ Y) ⊎ Z = (X ⊎ Z) ∪ (Y ⊎ Z).
Proof. by rewrite <-!(comm_L _ Z), gmultiset_disj_union_union_l. Qed.

(** Misc *)
Lemma gmultiset_non_empty_singleton x : {[ x ]} ≠@{gmultiset A} ∅.
Proof.
  rewrite gmultiset_eq. intros Hx; generalize (Hx x).
  by rewrite multiplicity_singleton, multiplicity_empty.
Qed.

(** Conversion from lists *)
Lemma list_to_set_disj_nil : list_to_set_disj [] =@{gmultiset A} ∅.
Proof. done. Qed.
Lemma list_to_set_disj_cons x l :
  list_to_set_disj (x :: l) =@{gmultiset A} {[ x ]} ⊎ list_to_set_disj l.
Proof. done. Qed.
Lemma list_to_set_disj_app l1 l2 :
  list_to_set_disj (l1 ++ l2) =@{gmultiset A} list_to_set_disj l1 ⊎ list_to_set_disj l2.
Proof.
  induction l1 as [|x l1 IH]; simpl.
  - by rewrite (left_id_L _ _).
  - by rewrite IH, (assoc_L _).
Qed.
Global Instance list_to_set_disj_perm :
  Proper ((≡ₚ) ==> (=)) (list_to_set_disj (C:=gmultiset A)).
Proof.
  induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; simpl; auto.
  - by rewrite IH.
  - by rewrite !(assoc_L _), (comm_L _ {[ x ]}).
  - by rewrite IH1.
Qed.

(** Properties of the elements operation *)
Lemma gmultiset_elements_empty : elements (∅ : gmultiset A) = [].
Proof.
  unfold elements, gmultiset_elements; simpl. by rewrite map_to_list_empty.
Qed.
Lemma gmultiset_elements_empty_inv X : elements X = [] → X = ∅.
Proof.
  destruct X as [X]; unfold elements, gmultiset_elements; simpl.
  intros; apply (f_equal GMultiSet). destruct (map_to_list X) as [|[]] eqn:?.
  - by apply map_to_list_empty_inv.
  - naive_solver.
Qed.
Lemma gmultiset_elements_empty' X : elements X = [] ↔ X = ∅.
Proof.
  split; intros HX; [by apply gmultiset_elements_empty_inv|].
  by rewrite HX, gmultiset_elements_empty.
Qed.
Lemma gmultiset_elements_singleton x : elements ({[ x ]} : gmultiset A) = [ x ].
Proof.
  unfold elements, gmultiset_elements; simpl. by rewrite map_to_list_singleton.
Qed.
Lemma gmultiset_elements_disj_union X Y :
  elements (X ⊎ Y) ≡ₚ elements X ++ elements Y.
Proof.
  destruct X as [X], Y as [Y]; unfold elements, gmultiset_elements.
  set (f xn := let '(x, n) := xn in replicate (S n) x); simpl.
  revert Y; induction X as [|x n X HX IH] using map_ind; intros Y.
  { by rewrite (left_id_L _ _ Y), map_to_list_empty. }
  destruct (Y !! x) as [n'|] eqn:HY.
  - rewrite <-(insert_id Y x n'), <-(insert_delete Y) by done.
    erewrite <-insert_union_with by done.
    rewrite !map_to_list_insert, !bind_cons
      by (by rewrite ?lookup_union_with, ?lookup_delete, ?HX).
    rewrite (assoc_L _), <-(comm (++) (f (_,n'))), <-!(assoc_L _), <-IH.
    rewrite (assoc_L _). f_equiv.
    rewrite (comm _); simpl. by rewrite replicate_plus, Permutation_middle.
  - rewrite <-insert_union_with_l, !map_to_list_insert, !bind_cons
      by (by rewrite ?lookup_union_with, ?HX, ?HY).
    by rewrite <-(assoc_L (++)), <-IH.
Qed.
Lemma gmultiset_elem_of_elements x X : x ∈ elements X ↔ x ∈ X.
Proof.
  destruct X as [X]. unfold elements, gmultiset_elements.
  set (f xn := let '(x, n) := xn in replicate (S n) x); simpl.
  unfold elem_of at 2, gmultiset_elem_of, multiplicity; simpl.
  rewrite elem_of_list_bind. split.
  - intros [[??] [[<- ?]%elem_of_replicate ->%elem_of_map_to_list]]; lia.
  - intros. destruct (X !! x) as [n|] eqn:Hx; [|lia].
    exists (x,n); split; [|by apply elem_of_map_to_list].
    apply elem_of_replicate; auto with lia.
Qed.
Lemma gmultiset_elem_of_dom x X : x ∈ dom (gset A) X ↔ x ∈ X.
Proof.
  unfold dom, gmultiset_dom, elem_of at 2, gmultiset_elem_of, multiplicity.
  destruct X as [X]; simpl; rewrite elem_of_dom, <-not_eq_None_Some.
  destruct (X !! x); naive_solver lia.
Qed.

(** Properties of the set_fold operation *)
Lemma gmultiset_set_fold_empty {B} (f : A → B → B) (b : B) :
  set_fold f b (∅ : gmultiset A) = b.
Proof. by unfold set_fold; simpl; rewrite gmultiset_elements_empty. Qed.
Lemma gmultiset_set_fold_singleton {B} (f : A → B → B) (b : B) (a : A) :
  set_fold f b ({[a]} : gmultiset A) = f a b.
Proof. by unfold set_fold; simpl; rewrite gmultiset_elements_singleton. Qed.
Lemma gmultiset_set_fold_disj_union (f : A → A → A) (b : A) X Y :
  Comm (=) f →
  Assoc (=) f →
  set_fold f b (X ⊎ Y) = set_fold f (set_fold f b X) Y.
Proof.
  intros Hcomm Hassoc. unfold set_fold; simpl.
  by rewrite gmultiset_elements_disj_union, <- foldr_app, (comm (++)).
Qed.

(** Properties of the size operation *)
Lemma gmultiset_size_empty : size (∅ : gmultiset A) = 0.
Proof. done. Qed.
Lemma gmultiset_size_empty_inv X : size X = 0 → X = ∅.
Proof.
  unfold size, gmultiset_size; simpl. rewrite length_zero_iff_nil.
  apply gmultiset_elements_empty_inv.
Qed.
Lemma gmultiset_size_empty_iff X : size X = 0 ↔ X = ∅.
Proof.
  split; [apply gmultiset_size_empty_inv|].
  by intros ->; rewrite gmultiset_size_empty.
Qed.
Lemma gmultiset_size_non_empty_iff X : size X ≠ 0 ↔ X ≠ ∅.
Proof. by rewrite gmultiset_size_empty_iff. Qed.

Lemma gmultiset_choose_or_empty X : (∃ x, x ∈ X) ∨ X = ∅.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - by apply gmultiset_elements_empty_inv.
  - exists x. rewrite <-gmultiset_elem_of_elements, HX. by left.
Qed.
Lemma gmultiset_choose X : X ≠ ∅ → ∃ x, x ∈ X.
Proof. intros. by destruct (gmultiset_choose_or_empty X). Qed.
Lemma gmultiset_size_pos_elem_of X : 0 < size X → ∃ x, x ∈ X.
Proof.
  intros Hsz. destruct (gmultiset_choose_or_empty X) as [|HX]; [done|].
  contradict Hsz. rewrite HX, gmultiset_size_empty; lia.
Qed.

Lemma gmultiset_size_singleton x : size ({[ x ]} : gmultiset A) = 1.
Proof.
  unfold size, gmultiset_size; simpl. by rewrite gmultiset_elements_singleton.
Qed.
Lemma gmultiset_size_disj_union X Y : size (X ⊎ Y) = size X + size Y.
Proof.
  unfold size, gmultiset_size; simpl.
  by rewrite gmultiset_elements_disj_union, app_length.
Qed.

(** Order stuff *)
Global Instance gmultiset_po : PartialOrder (⊆@{gmultiset A}).
Proof.
  split; [split|].
  - by intros X x.
  - intros X Y Z HXY HYZ x. by trans (multiplicity x Y).
  - intros X Y HXY HYX; apply gmultiset_eq; intros x. by apply (anti_symm (≤)).
Qed.

Lemma gmultiset_subseteq_alt X Y :
  X ⊆ Y ↔
  map_relation (≤) (λ _, False) (λ _, True) (gmultiset_car X) (gmultiset_car Y).
Proof.
  apply forall_proper; intros x. unfold multiplicity.
  destruct (gmultiset_car X !! x), (gmultiset_car Y !! x); naive_solver lia.
Qed.
Global Instance gmultiset_subseteq_dec : RelDecision (⊆@{gmultiset A}).
Proof.
 refine (λ X Y, cast_if (decide (map_relation (≤)
   (λ _, False) (λ _, True) (gmultiset_car X) (gmultiset_car Y))));
   by rewrite gmultiset_subseteq_alt.
Defined.

Lemma gmultiset_subset_subseteq X Y : X ⊂ Y → X ⊆ Y.
Proof. apply strict_include. Qed.
Hint Resolve gmultiset_subset_subseteq : core.

Lemma gmultiset_empty_subseteq X : ∅ ⊆ X.
Proof. intros x. rewrite multiplicity_empty. lia. Qed.

Lemma gmultiset_union_subseteq_l X Y : X ⊆ X ∪ Y.
Proof. intros x. rewrite multiplicity_union. lia. Qed.
Lemma gmultiset_union_subseteq_r X Y : Y ⊆ X ∪ Y.
Proof. intros x. rewrite multiplicity_union. lia. Qed.
Lemma gmultiset_union_mono X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
Proof.
  intros HX HY x. rewrite !multiplicity_union.
  specialize (HX x); specialize (HY x); lia.
Qed.
Lemma gmultiset_union_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
Proof. intros. by apply gmultiset_union_mono. Qed.
Lemma gmultiset_union_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
Proof. intros. by apply gmultiset_union_mono. Qed.

Lemma gmultiset_disj_union_subseteq_l X Y : X ⊆ X ⊎ Y.
Proof. intros x. rewrite multiplicity_disj_union. lia. Qed.
Lemma gmultiset_disj_union_subseteq_r X Y : Y ⊆ X ⊎ Y.
Proof. intros x. rewrite multiplicity_disj_union. lia. Qed.
Lemma gmultiset_disj_union_mono X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ⊎ Y1 ⊆ X2 ⊎ Y2.
Proof. intros ?? x. rewrite !multiplicity_disj_union. by apply Nat.add_le_mono. Qed.
Lemma gmultiset_disj_union_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ⊎ Y1 ⊆ X ⊎ Y2.
Proof. intros. by apply gmultiset_disj_union_mono. Qed.
Lemma gmultiset_disj_union_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ⊎ Y ⊆ X2 ⊎ Y.
Proof. intros. by apply gmultiset_disj_union_mono. Qed.

Lemma gmultiset_subset X Y : X ⊆ Y → size X < size Y → X ⊂ Y.
Proof. intros. apply strict_spec_alt; split; naive_solver auto with lia. Qed.
Lemma gmultiset_disj_union_subset_l X Y : Y ≠ ∅ → X ⊂ X ⊎ Y.
Proof.
  intros HY%gmultiset_size_non_empty_iff.
  apply gmultiset_subset; auto using gmultiset_disj_union_subseteq_l.
  rewrite gmultiset_size_disj_union; lia.
Qed.
Lemma gmultiset_union_subset_r X Y : X ≠ ∅ → Y ⊂ X ⊎ Y.
Proof. rewrite (comm_L (⊎)). apply gmultiset_disj_union_subset_l. Qed.

Lemma gmultiset_elem_of_singleton_subseteq x X : x ∈ X ↔ {[ x ]} ⊆ X.
Proof.
  rewrite elem_of_multiplicity. split.
  - intros Hx y. rewrite multiplicity_singleton'.
    destruct (decide (y = x)); naive_solver lia.
  - intros Hx. generalize (Hx x). rewrite multiplicity_singleton. lia.
Qed.

Lemma gmultiset_elem_of_subseteq X1 X2 x : x ∈ X1 → X1 ⊆ X2 → x ∈ X2.
Proof. rewrite !gmultiset_elem_of_singleton_subseteq. by intros ->. Qed.

Lemma gmultiset_disj_union_difference X Y : X ⊆ Y → Y = X ⊎ Y ∖ X.
Proof.
  intros HXY. apply gmultiset_eq; intros x; specialize (HXY x).
  rewrite multiplicity_disj_union, multiplicity_difference; lia.
Qed.
Lemma gmultiset_disj_union_difference' x Y : x ∈ Y → Y = {[ x ]} ⊎ Y ∖ {[ x ]}.
Proof.
  intros. by apply gmultiset_disj_union_difference,
    gmultiset_elem_of_singleton_subseteq.
Qed.

Lemma gmultiset_size_difference X Y : Y ⊆ X → size (X ∖ Y) = size X - size Y.
Proof.
  intros HX%gmultiset_disj_union_difference.
  rewrite HX at 2; rewrite gmultiset_size_disj_union. lia.
Qed.

Lemma gmultiset_empty_difference X Y : Y ⊆ X → Y ∖ X = ∅.
Proof.
  intros HYX. unfold_leibniz. intros x.
  rewrite multiplicity_difference, multiplicity_empty.
  specialize (HYX x). lia.
Qed.

Lemma gmultiset_non_empty_difference X Y : X ⊂ Y → Y ∖ X ≠ ∅.
Proof.
  intros [_ HXY2] Hdiff; destruct HXY2; intros x.
  generalize (f_equal (multiplicity x) Hdiff).
  rewrite multiplicity_difference, multiplicity_empty; lia.
Qed.

Lemma gmultiset_difference_diag X : X ∖ X = ∅.
Proof. by apply gmultiset_empty_difference. Qed.

Lemma gmultiset_difference_subset X Y : X ≠ ∅ → X ⊆ Y → Y ∖ X ⊂ Y.
Proof.
  intros. eapply strict_transitive_l; [by apply gmultiset_union_subset_r|].
  by rewrite <-(gmultiset_disj_union_difference X Y).
Qed.

(** Mononicity *)
Lemma gmultiset_elements_submseteq X Y : X ⊆ Y → elements X ⊆+ elements Y.
Proof.
  intros ->%gmultiset_disj_union_difference. rewrite gmultiset_elements_disj_union.
  by apply submseteq_inserts_r.
Qed.

Lemma gmultiset_subseteq_size X Y : X ⊆ Y → size X ≤ size Y.
Proof. intros. by apply submseteq_length, gmultiset_elements_submseteq. Qed.

Lemma gmultiset_subset_size X Y : X ⊂ Y → size X < size Y.
Proof.
  intros HXY. assert (size (Y ∖ X) ≠ 0).
  { by apply gmultiset_size_non_empty_iff, gmultiset_non_empty_difference. }
  rewrite (gmultiset_disj_union_difference X Y),
    gmultiset_size_disj_union by auto. lia.
Qed.

(** Well-foundedness *)
Lemma gmultiset_wf : wf (⊂@{gmultiset A}).
Proof.
  apply (wf_projected (<) size); auto using gmultiset_subset_size, lt_wf.
Qed.

Lemma gmultiset_ind (P : gmultiset A → Prop) :
  P ∅ → (∀ x X, P X → P ({[ x ]} ⊎ X)) → ∀ X, P X.
Proof.
  intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
  destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' x X) by done.
  apply Hinsert, IH, gmultiset_difference_subset,
    gmultiset_elem_of_singleton_subseteq; auto using gmultiset_non_empty_singleton.
Qed.
End lemmas.
