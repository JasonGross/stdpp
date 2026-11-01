(** This files implements an efficient implementation of finite maps whose keys
range over Rocq's data type of any countable type [K].

This version is a prototype that builds [gmap] on the standard library's
canonical trie [Trie] (through [Pmap], which is [trie A] on this branch): a
[gmap K A] is a dependent pair of a [Pmap A] and a proof that every position in
the trie is a valid encoding of [K]. Following a suggestion by Andres Erbsen,
the core type [gmap_dep A P] is parametrized by a boolean validity predicate
[P : positive → A → bool] on the bindings, and the proof is
[Is_true (forallb P (Trie.to_list m))], which is proof irrelevant.

Compared to std++'s [gmap_dep_ne A P] (a trie with the predicate in its type),
this is much shorter and all map laws come from the [Pmap] instance. The price
is strict positivity: a dependent pair cannot be used in nested recursive
definitions such as [Inductive gtest := GTest : gmap K gtest → gtest]. *)
From stdpp Require Export countable finite infinite fin_maps fin_map_dom.
From stdpp Require Import mapset pmap.
From Trie Require Import Trie.
From Stdlib Require Import SetoidList StrictProp.
From stdpp Require Import options.

Local Open Scope positive_scope.

(** * Validity of a trie with respect to a predicate on its bindings *)
Definition map_valid {A} (P : positive → A → bool) (m : Pmap A) : bool :=
  forallb (λ '(k,x), P k x) (Trie.to_list m).

Local Lemma InA_eq_key_elt {A} (p : positive * A) l :
  InA (@Trie.FMap.eq_key_elt A) p l ↔ p ∈ l.
Proof.
  rewrite InA_alt, list_elem_of_In. split.
  - intros ([k x] & [Hk Hx] & ?). destruct p as [k' x']; simpl in *.
    unfold Trie.FMap.E.eq in Hk. by simplify_eq.
  - intros ?. exists p. split; [|done]. destruct p; split; reflexivity.
Qed.

Lemma map_valid_spec {A} (P : positive → A → bool) (m : Pmap A) :
  map_valid P m ↔ ∀ i x, m !! i = Some x → P i x.
Proof.
  unfold map_valid. rewrite Is_true_true, forallb_forall. split.
  - intros Hall i x Hi. apply Is_true_true. apply (Hall (i,x)).
    apply list_elem_of_In, InA_eq_key_elt. by apply Trie.FMap.elements_spec.
  - intros Hall [i x] Hin. apply Is_true_true. apply Hall.
    by apply Trie.FMap.elements_spec, InA_eq_key_elt, list_elem_of_In.
Qed.

Lemma map_valid_empty {A} (P : positive → A → bool) : map_valid P ∅.
Proof. apply map_valid_spec. intros i x. by rewrite lookup_empty. Qed.
Lemma map_valid_partial_alter {A} (P : positive → A → bool) f i (m : Pmap A) :
  (∀ x, P i x) → map_valid P m → map_valid P (partial_alter f i m).
Proof.
  rewrite !map_valid_spec. intros HP Hm j x.
  destruct (decide (i = j)) as [->|]; [done|].
  rewrite lookup_partial_alter_ne by done. apply Hm.
Qed.
Lemma map_valid_fmap {A B} (P : positive → A → bool) (Q : positive → B → bool)
    (f : A → B) (m : Pmap A) :
  (∀ i x, P i x → Q i (f x)) → map_valid P m → map_valid Q (f <$> m).
Proof.
  rewrite !map_valid_spec. intros HPQ Hm i y.
  rewrite lookup_fmap. destruct (m !! i) as [x|] eqn:?; [|done].
  intros [= <-]. eauto.
Qed.
Lemma map_valid_omap {A B} (P : positive → A → bool) (Q : positive → B → bool)
    (f : A → option B) (m : Pmap A) :
  (∀ i x y, P i x → f x = Some y → Q i y) → map_valid P m → map_valid Q (omap f m).
Proof.
  rewrite !map_valid_spec. intros HPQ Hm i y.
  rewrite lookup_omap. destruct (m !! i) as [x|] eqn:?; [|done]. simpl. eauto.
Qed.
Lemma map_valid_merge {A B C} (P : positive → A → bool) (Q : positive → B → bool)
    (R : positive → C → bool) (f : option A → option B → option C)
    (m1 : Pmap A) (m2 : Pmap B) :
  (∀ i x z, P i x → R i z) → (∀ i y z, Q i y → R i z) →
  map_valid P m1 → map_valid Q m2 → map_valid R (merge f m1 m2).
Proof.
  rewrite !map_valid_spec. intros HPR HQR Hm1 Hm2 i z.
  rewrite lookup_merge. unfold diag_None.
  destruct (m1 !! i) as [x|] eqn:?, (m2 !! i) as [y|] eqn:?; eauto; done.
Qed.

(** The validity proof lives in [SProp], so that it is definitionally proof
irrelevant: two [gmap_dep] values with the same trie are convertible, and
[reflexivity] proves [{[3:=false; 2:=true]} = {[2:=true; 3:=false]}] as before.
With a [Prop] proof this does not hold: an opaque proof makes the two sides
differ syntactically, and a transparent proof that computes to [I] forces
[vm_compute] and conversion to re-check [map_valid] over the whole map at every
operation, which is quadratic. *)
Definition sIs_true (b : bool) : SProp := if b then sUnit else sEmpty.
Lemma sIs_true_intro (b : bool) : Is_true b → sIs_true b.
Proof. destruct b; [intros _; exact stt|intros []]. Qed.
Lemma sIs_true_elim (b : bool) : sIs_true b → Is_true b.
Proof. destruct b; [intros _; exact I|intros []]. Qed.

(** The [SProp] versions of the validity lemmas. Their arguments are only the
data (the predicate, the function, the key, the trie and the previous proof),
never a [map_valid ...] term, so that [vm_compute] does not evaluate
[map_valid] of every intermediate map: the proof components stay inert. *)
Lemma map_valid_empty_s {A} (P : positive → A → bool) : sIs_true (map_valid P ∅).
Proof. apply sIs_true_intro, map_valid_empty. Qed.
Lemma map_valid_partial_alter_s {A} (P : positive → A → bool) f i (m : Pmap A) :
  (∀ x, P i x) → sIs_true (map_valid P m) → sIs_true (map_valid P (partial_alter f i m)).
Proof. intros ? ?%sIs_true_elim. by apply sIs_true_intro, map_valid_partial_alter. Qed.
Lemma map_valid_fmap_s {A B} (P : positive → A → bool) (Q : positive → B → bool)
    (f : A → B) (m : Pmap A) :
  (∀ i x, P i x → Q i (f x)) → sIs_true (map_valid P m) → sIs_true (map_valid Q (f <$> m)).
Proof. intros ? ?%sIs_true_elim. by apply sIs_true_intro, (map_valid_fmap P). Qed.
Lemma map_valid_omap_s {A B} (P : positive → A → bool) (Q : positive → B → bool)
    (f : A → option B) (m : Pmap A) :
  (∀ i x y, P i x → f x = Some y → Q i y) →
  sIs_true (map_valid P m) → sIs_true (map_valid Q (omap f m)).
Proof. intros ? ?%sIs_true_elim. by apply sIs_true_intro, (map_valid_omap P). Qed.
Lemma map_valid_merge_s {A B C} (P : positive → A → bool) (Q : positive → B → bool)
    (R : positive → C → bool) (f : option A → option B → option C)
    (m1 : Pmap A) (m2 : Pmap B) :
  (∀ i x z, P i x → R i z) → (∀ i y z, Q i y → R i z) →
  sIs_true (map_valid P m1) → sIs_true (map_valid Q m2) →
  sIs_true (map_valid R (merge f m1 m2)).
Proof.
  intros ? ? ?%sIs_true_elim ?%sIs_true_elim.
  by apply sIs_true_intro, (map_valid_merge P Q).
Qed.

(** * The dependent pair *)
(** The first component is written [option (branch A)], which is what [Pmap A]
unfolds to: [branch] is template polymorphic, [Pmap] (a definition) is not,
and [gmap Z Z : Set] must hold. *)
Record gmap_dep (A : Type) (P : positive → A → bool) := GMapDep {
  gmap_dep_car : option (branch A);
  gmap_dep_prf : sIs_true (map_valid P gmap_dep_car)
}.
Add Printing Constructor gmap_dep.
Global Arguments GMapDep {_ _} _ _.
Global Arguments gmap_dep_car {_ _} _.
Global Arguments gmap_dep_prf {_ _} _.
Definition gmap_dep_pmap {A P} (m : gmap_dep A P) : Pmap A := gmap_dep_car m.

Lemma gmap_dep_eq {A P} (m1 m2 : gmap_dep A P) :
  gmap_dep_pmap m1 = gmap_dep_pmap m2 → m1 = m2.
Proof.
  destruct m1 as [t1 p1], m2 as [t2 p2]; unfold gmap_dep_pmap; simpl; intros <-.
  reflexivity.
Qed.
Global Instance gmap_dep_eq_dec {A P} `{EqDecision A} : EqDecision (gmap_dep A P).
Proof.
  refine (λ m1 m2, cast_if (decide (gmap_dep_pmap m1 = gmap_dep_pmap m2)));
    abstract (first [by apply gmap_dep_eq|by intros ->]).
Defined.

(** Positions that are valid encodings of [K] *)
Definition gmap_key_ok K `{Countable K} (i : positive) : bool :=
  bool_decide (encode (A:=K) <$> decode i = Some i).
Lemma gmap_key_ok_encode `{Countable K} (k : K) : gmap_key_ok K (encode k).
Proof. apply bool_decide_pack. by rewrite decode_encode. Qed.
Lemma gmap_key_ok_decode `{Countable K} i :
  gmap_key_ok K i → ∃ k : K, decode i = Some k ∧ encode k = i.
Proof.
  intros Hi%bool_decide_unpack. destruct (decode i) as [k|]; simplify_eq/=.
  by exists k.
Qed.

Record gmap K `{Countable K} A := GMap {
  gmap_car : gmap_dep A (λ i _, gmap_key_ok K i)
}.
Add Printing Constructor gmap.
Global Arguments GMap {_ _ _ _} _.
Global Arguments gmap_car {_ _ _ _} _.

Global Instance gmap_eq_dec `{Countable K} {A} :
  EqDecision A → EqDecision (gmap K A).
Proof. intros. solve_decision. Defined.

(** Operations: all of them are the [Pmap] operations on the first component,
with the validity proof carried along. *)
Global Instance gmap_lookup `{Countable K} {A} :
    Lookup K A (gmap K A) := λ k m,
  gmap_dep_pmap (gmap_car m) !! encode k.

Global Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) :=
  GMap (GMapDep ∅ (map_valid_empty_s _)).

(** Block reduction, even on concrete [gmap]s, as in std++. *)
Global Opaque gmap_empty.

Global Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f k '(GMap (GMapDep t p)),
  let t : Pmap A := t in
  GMap (GMapDep (partial_alter f (encode k) t)
    (map_valid_partial_alter_s _ f (encode k) t (λ _, gmap_key_ok_encode k) p)).

Global Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ {A B} f '(GMap (GMapDep t p)),
  let t : Pmap A := t in
  GMap (GMapDep (f <$> t)
    (map_valid_fmap_s (λ i _, gmap_key_ok K i) (λ i _, gmap_key_ok K i) f t (λ _ _ H, H) p)).

Global Instance gmap_omap `{Countable K} : OMap (gmap K) := λ {A B} f '(GMap (GMapDep t p)),
  let t : Pmap A := t in
  GMap (GMapDep (omap f t)
    (map_valid_omap_s (λ i _, gmap_key_ok K i) (λ i _, gmap_key_ok K i) f t (λ _ _ _ H _, H) p)).

Global Instance gmap_merge `{Countable K} : Merge (gmap K) :=
  λ {A B C} f '(GMap (GMapDep t1 p1)) '(GMap (GMapDep t2 p2)),
  let t1 : Pmap A := t1 in let t2 : Pmap B := t2 in
  GMap (GMapDep (merge f t1 t2)
    (map_valid_merge_s (λ i _, gmap_key_ok K i) (λ i _, gmap_key_ok K i) (λ i _, gmap_key_ok K i)
       f t1 t2 (λ _ _ _ H, H) (λ _ _ _ H, H) p1 p2)).

Global Instance gmap_fold `{Countable K} {A} :
    MapFold K A (gmap K A) := λ {B} f y '(GMap (GMapDep t _)),
  map_fold (λ i x, match decode i with Some k => f k x | None => id end) y (t : Pmap A).

(** * Proofs *)
Local Lemma gmap_eq `{Countable K} {A} (m1 m2 : gmap K A) :
  gmap_dep_pmap (gmap_car m1) = gmap_dep_pmap (gmap_car m2) → m1 = m2.
Proof. destruct m1 as [m1], m2 as [m2]; simpl; intros. f_equal. by apply gmap_dep_eq. Qed.

Local Lemma gmap_lookup_car `{Countable K} {A} (m : gmap K A) i :
  gmap_dep_pmap (gmap_car m) !! i =
    match decode i with
    | Some k => if decide (encode k = i) then m !! k else None
    | None => None
    end.
Proof.
  unfold lookup at 2, gmap_lookup. set (t := gmap_dep_pmap (gmap_car m)).
  pose proof (sIs_true_elim _ (gmap_dep_prf (gmap_car m))) as p.
  change (Is_true (map_valid (λ i _, gmap_key_ok K i) t)) in p.
  rewrite map_valid_spec in p.
  destruct (decode i) as [k|] eqn:Hd.
  - destruct (decide (encode k = i)) as [->|Hne]; [done|].
    destruct (t !! i) as [x|] eqn:Ht; [|done]. exfalso.
    specialize (p _ _ Ht). apply bool_decide_unpack in p. rewrite Hd in p. naive_solver.
  - destruct (t !! i) as [x|] eqn:Ht; [|done]. exfalso.
    specialize (p _ _ Ht). apply bool_decide_unpack in p. by rewrite Hd in p.
Qed.

Local Lemma gmap_fold_car `{Countable K} {A B} (f : K → A → B → B) b (m : gmap K A) :
  map_fold f b m =
    map_fold (λ i x, match decode i with Some k => f k x | None => id end) b
      (gmap_dep_pmap (gmap_car m)).
Proof. by destruct m as [[t p]]. Qed.
Local Lemma gmap_insert_car `{Countable K} {A} k x (m : gmap K A) :
  gmap_dep_pmap (gmap_car (<[k:=x]> m)) = <[encode k:=x]> (gmap_dep_pmap (gmap_car m)).
Proof. by destruct m as [[t p]]. Qed.
Local Lemma gmap_fmap_car `{Countable K} {A B} (g : A → B) (m : gmap K A) :
  gmap_dep_pmap (gmap_car (g <$> m)) = g <$> gmap_dep_pmap (gmap_car m).
Proof. by destruct m as [[t p]]. Qed.

(** Instance of the finite map type class *)
Global Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Proof.
  split.
  - intros A m1 m2 Hlookup. apply gmap_eq, map_eq. intros i.
    rewrite !gmap_lookup_car. destruct (decode i) as [k|]; [|done].
    destruct (decide (encode k = i)); [apply Hlookup|done].
  - done.
  - intros A f [[t p]] k. apply (lookup_partial_alter_eq (M:=Pmap)).
  - intros A f [[t p]] k1 k2 ?. apply (lookup_partial_alter_ne (M:=Pmap)).
    intros ?%encode_inj. done.
  - intros A B f [[t p]] k. apply (lookup_fmap (M:=Pmap)).
  - intros A B f [[t p]] k. apply (lookup_omap (M:=Pmap)).
  - intros A B C f [[t1 p1]] [[t2 p2]] k. apply (lookup_merge (M:=Pmap)).
  - done.
  - intros A Q Hemp Hins [[t p]]. change (Pmap A) in t. revert p.
    induction t as [|i x t Ht Hfold IH] using (map_fold_fmap_ind (M:=Pmap)); intros p.
    { apply Hemp. }
    pose proof (sIs_true_elim _ p) as pI. rewrite map_valid_spec in pI.
    assert (sIs_true (map_valid (λ i _, gmap_key_ok K i) t)) as p'.
    { apply sIs_true_intro, map_valid_spec. intros j y Hj.
      apply (pI j y). rewrite lookup_insert_ne; [done|]. naive_solver. }
    assert (gmap_key_ok K i) as Hi.
    { apply (pI i x). apply lookup_insert_eq. }
    destruct (gmap_key_ok_decode _ Hi) as (k & Hk & Hki).
    assert (GMap (GMapDep (<[i:=x]> t) p) = <[k:=x]> (GMap (GMapDep t p'))) as ->.
    { apply gmap_eq; simpl. by rewrite Hki. }
    apply (Hins k x (GMap (GMapDep t p'))).
    + unfold lookup, gmap_lookup; simpl. by rewrite Hki.
    + intros A' B f g b x'.
      rewrite !gmap_fold_car, gmap_insert_car, !gmap_fmap_car; simpl.
      rewrite Hki, (Hfold _ _ _ g b x'). cbv beta. by rewrite Hk.
    + apply IH.
Qed.

Global Program Instance gmap_countable `{Countable K, Countable A} :
  Countable (gmap K A) := map_countable.

Global Program Instance gmap_finite `{Finite K, Finite A} : Finite (gmap K A) :=
  map_finite.

(** Conversion to/from [Pmap] *)
Definition gmap_to_pmap {A} (m : gmap positive A) : Pmap A :=
  gmap_dep_pmap (gmap_car m).
Lemma lookup_gmap_to_pmap {A} (m : gmap positive A) i :
  gmap_to_pmap m !! i = m !! i.
Proof. done. Qed.

Lemma map_valid_positive {A} (m : Pmap A) :
  map_valid (λ i _, gmap_key_ok positive i) m.
Proof. apply map_valid_spec. intros i x _. by apply bool_decide_pack. Qed.
Definition pmap_to_gmap {A} (m : Pmap A) : gmap positive A :=
  GMap (GMapDep m (sIs_true_intro _ (map_valid_positive m))).
Lemma lookup_pmap_to_gmap {A} (m : Pmap A) i : pmap_to_gmap m !! i = m !! i.
Proof. done. Qed.

(** * Finite sets *)
Definition gset K `{Countable K} := mapset (gmap K).

Section gset.
  Context `{Countable K}.
  (* Lift instances of operational TCs from [mapset] and mark them [simpl never]. *)
  Global Instance gset_elem_of: ElemOf K (gset K) := _.
  Global Instance gset_empty : Empty (gset K) := _.
  Global Instance gset_singleton : Singleton K (gset K) := _.
  Global Instance gset_union: Union (gset K) := _.
  Global Instance gset_intersection: Intersection (gset K) := _.
  Global Instance gset_difference: Difference (gset K) := _.
  Global Instance gset_elements: Elements K (gset K) := _.
  Global Instance gset_eq_dec : EqDecision (gset K) := _.
  Global Instance gset_countable : Countable (gset K) := _.
  Global Instance gset_equiv_dec : RelDecision (≡@{gset K}) | 1 := _.
  Global Instance gset_elem_of_dec : RelDecision (∈@{gset K}) | 1 := _.
  Global Instance gset_disjoint_dec : RelDecision (##@{gset K}) := _.
  Global Instance gset_subseteq_dec : RelDecision (⊆@{gset K}) := _.

  (** We put in an eta expansion to avoid [injection] from unfolding equalities
  like [dom (gset _) m1 = dom (gset _) m2]. *)
  Global Instance gset_dom {A} : Dom (gmap K A) (gset K) := λ m,
    let '(GMap mt) := m in mapset_dom (GMap mt).

  Global Arguments gset_elem_of : simpl never.
  Global Arguments gset_empty : simpl never.
  Global Arguments gset_singleton : simpl never.
  Global Arguments gset_union : simpl never.
  Global Arguments gset_intersection : simpl never.
  Global Arguments gset_difference : simpl never.
  Global Arguments gset_elements : simpl never.
  Global Arguments gset_eq_dec : simpl never.
  Global Arguments gset_countable : simpl never.
  Global Arguments gset_equiv_dec : simpl never.
  Global Arguments gset_elem_of_dec : simpl never.
  Global Arguments gset_disjoint_dec : simpl never.
  Global Arguments gset_subseteq_dec : simpl never.
  Global Arguments gset_dom : simpl never.

  (* Lift instances of other TCs. *)
  Global Instance gset_leibniz : LeibnizEquiv (gset K) := _.
  Global Instance gset_semi_set : SemiSet K (gset K) | 1 := _.
  Global Instance gset_set : Set_ K (gset K) | 1 := _.
  Global Instance gset_fin_set : FinSet K (gset K) := _.
  Global Instance gset_dom_spec : FinMapDom K (gmap K) (gset K).
  Proof.
    pose proof (mapset_dom_spec (M:=gmap K)) as [?? Hdom]; split; auto.
    intros A m. specialize (Hdom A m). by destruct m.
  Qed.

  (** If you are looking for a lemma showing that [gset] is extensional, see
  [sets.set_eq]. *)

  (** The function [gset_to_gmap x X] converts a set [X] to a map with domain
  [X] where each key has value [x]. Compared to the generic conversion
  [set_to_map], the function [gset_to_gmap] has [O(n)] instead of [O(n log n)]
  complexity and has an easier and better developed theory. *)

  Definition gset_to_gmap {A} (x : A) (X : gset K) : gmap K A :=
    (λ _, x) <$> mapset_car X.

  Lemma lookup_gset_to_gmap {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = (guard (i ∈ X);; Some x).
  Proof.
    destruct X as [X].
    unfold gset_to_gmap, gset_elem_of, elem_of, mapset_elem_of; simpl.
    rewrite lookup_fmap.
    case_guard; destruct (X !! i) as [[]|]; naive_solver.
  Qed.
  Lemma lookup_gset_to_gmap_Some {A} (x : A) (X : gset K) i y :
    gset_to_gmap x X !! i = Some y ↔ i ∈ X ∧ x = y.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.
  Lemma lookup_gset_to_gmap_None {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = None ↔ i ∉ X.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.

  Lemma gset_to_gmap_empty {A} (x : A) : gset_to_gmap x ∅ = ∅.
  Proof. apply fmap_empty. Qed.
  Lemma gset_to_gmap_union_singleton {A} (x : A) i Y :
    gset_to_gmap x ({[ i ]} ∪ Y) = <[i:=x]>(gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_insert_Some, !lookup_gset_to_gmap_Some, elem_of_union,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.
  Lemma gset_to_gmap_singleton {A} (x : A) i :
    gset_to_gmap x {[ i ]} = {[i:=x]}.
  Proof.
    rewrite <-(right_id_L ∅ (∪) {[ i ]}), gset_to_gmap_union_singleton.
    by rewrite gset_to_gmap_empty.
  Qed.
  Lemma gset_to_gmap_difference_singleton {A} (x : A) i Y :
    gset_to_gmap x (Y ∖ {[i]}) = delete i (gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_delete_Some, !lookup_gset_to_gmap_Some, elem_of_difference,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.

  Lemma fmap_gset_to_gmap {A B} (f : A → B) (X : gset K) (x : A) :
    f <$> gset_to_gmap x X = gset_to_gmap (f x) X.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, !lookup_gset_to_gmap.
    by simplify_option_eq.
  Qed.
  Lemma gset_to_gmap_dom {A B} (m : gmap K A) (y : B) :
    gset_to_gmap y (dom m) = const y <$> m.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, lookup_gset_to_gmap.
    destruct (m !! j) as [x|] eqn:?.
    - by rewrite option_guard_True by (rewrite elem_of_dom; eauto).
    - by rewrite option_guard_False by (rewrite not_elem_of_dom; eauto).
  Qed.
  Lemma dom_gset_to_gmap {A} (X : gset K) (x : A) :
    dom (gset_to_gmap x X) = X.
  Proof.
    induction X as [| y X not_in IH] using set_ind_L.
    - rewrite gset_to_gmap_empty, dom_empty_L; done.
    - rewrite gset_to_gmap_union_singleton, dom_insert_L, IH; done.
  Qed.

  Lemma gset_to_gmap_set_to_map {A} (X : gset K) (x : A) :
    gset_to_gmap x X = set_to_map (λ _, x) X.
  Proof.
    apply map_eq; intros k. by rewrite lookup_gset_to_gmap, lookup_set_to_map.
  Qed.

  Lemma map_to_list_gset_to_gmap {A} (X : gset K) (x : A) :
    map_to_list (gset_to_gmap x X) ≡ₚ (., x) <$> elements X.
  Proof.
    induction X as [| y X not_in IH] using set_ind_L.
    - rewrite gset_to_gmap_empty, elements_empty, map_to_list_empty. done.
    - rewrite gset_to_gmap_union_singleton, elements_union_singleton by done.
      rewrite map_to_list_insert.
      2:{ rewrite lookup_gset_to_gmap_None. done. }
      rewrite IH. done.
  Qed.
End gset.

Section gset_cprod.
  Context `{Countable A, Countable B}.

  Global Instance gset_cprod : CProd (gset A) (gset B) (gset (A * B)) :=
    λ X Y, set_bind (λ e1, set_map (e1,.) Y) X.

  Lemma elem_of_gset_cprod (X : gset A) (Y : gset B) x :
    x ∈ cprod X Y ↔ x.1 ∈ X ∧ x.2 ∈ Y.
  Proof. unfold cprod, gset_cprod. destruct x. set_solver. Qed.

  Global Instance set_unfold_gset_cprod (X : gset A) (Y : gset B) x (P : Prop) Q :
    SetUnfoldElemOf x.1 X P → SetUnfoldElemOf x.2 Y Q →
    SetUnfoldElemOf x (cprod X Y) (P ∧ Q).
  Proof using.
    intros ??; constructor.
    by rewrite elem_of_gset_cprod, (set_unfold_elem_of x.1 X P),
      (set_unfold_elem_of x.2 Y Q).
  Qed.

End gset_cprod.

Global Typeclasses Opaque gset.
