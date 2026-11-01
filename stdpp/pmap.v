(** This files implements an efficient implementation of finite maps whose keys
range over Rocq's data type of positive binary naturals [positive]. The
data structure is based on the "canonical" binary tries representation by Appel
and Leroy, https://hal.inria.fr/hal-03372247. It has various good properties:

- It guarantees logarithmic-time [lookup] and [partial_alter], and linear-time
  [merge]. It has a low constant factor for computation in Rocq compared to other
  versions (see the Appel and Leroy paper for benchmarks).
- It satisfies extensional equality, i.e., [(∀ i, m1 !! i = m2 !! i) → m1 = m2].
- It can be used in nested recursive definitions, e.g.,
  [Inductive test := Test : Pmap test → test]. This is possible because we do
  _not_ use a Sigma type to ensure canonical representations (a Sigma type would
  break Rocq's strict positivity check).

This version of the file is a wrapper around the standard library's [Trie]
([Stdlib.EMaps.Trie], here the vendored copy [Trie.Trie]), which is the same
canonical trie: [Pmap_ne A] is [branch A] and [Pmap A] is [trie A], i.e.
[option (branch A)]. [lookup], [partial_alter], [fmap], [omap] and [merge] are
the [Trie] operations [get], [set]/[remove], [map_filter] and [combine];
[map_fold] is std++'s own structural fold, because [Trie] only has a fold
through [elements] (the [FMapInterface] one). *)
From stdpp Require Export countable finite fin_maps fin_map_dom.
From stdpp Require Import mapset.
From Trie Require Import Trie.
From stdpp Require Import options.

Local Open Scope positive_scope.

(** * The trie data structure *)
(** [Pmap_ne A] is the type of non-empty canonical tries, [Pmap A] adds the
empty trie. These are [Trie.branch] and [Trie.trie]. *)
Notation Pmap_ne := branch.
Notation PNode001 := Node001.
Notation PNode010 := Node010.
Notation PNode011 := Node011.
Notation PNode100 := Node100.
Notation PNode101 := Node101.
Notation PNode110 := Node110.
Notation PNode111 := Node111.

Definition Pmap (A : Type) : Type := trie A.
(** [Pmap A] unfolds to [option (Pmap_ne A)]; without this, type class search
would also find the [option] instances (for example [option_union], which
made [m1 ∪ m2] return [m1]). *)
Global Typeclasses Opaque Pmap.
Notation PEmpty := (@None _) (only parsing).
Notation PNodes := (@Some _) (only parsing).

Global Instance Pmap_ne_eq_dec `{EqDecision A} : EqDecision (Pmap_ne A).
Proof. solve_decision. Defined.
Global Instance Pmap_eq_dec `{EqDecision A} : EqDecision (Pmap A).
Proof. unfold Pmap, trie. apply _. Defined.

(** The smart constructor [PNode] and eliminator [Pmap_ne_case] are used to
reduce the number of cases, similar to Appel and Leroy. *)
Local Definition PNode {A} (ml : Pmap A) (mx : option A) (mr : Pmap A) : Pmap A :=
  Node ml mx mr.
Local Definition Pmap_ne_case {A B} (t : Pmap_ne A)
    (f : Pmap A → option A → Pmap A → B) : B := branch_map f t.

(** Operations *)
Global Instance Pmap_lookup {A} : Lookup positive A (Pmap A) := get.
(** [get i (Some t)] unfolds to this ([Trie.get'] is the fixpoint behind
[get]); written this way so that [simpl] computes it on a constructor. *)
Global Instance Pmap_ne_lookup {A} : Lookup positive A (Pmap_ne A) := λ i t,
  Trie.get' t i.
Global Arguments Pmap_ne_lookup {_} _ !_ / : assert.
Global Arguments Pmap_lookup {_} _ !_ / : assert.
Local Arguments lookup _ _ _ _ _ !_ / : simpl nomatch, assert.

Global Instance Pmap_empty {A} : Empty (Pmap A) := PEmpty.

(** Block reduction, even on concrete [Pmap]s.
Marking [Pmap_empty] as [simpl never] would not be enough, because of
https://github.com/rocq-prover/rocq/issues/2972 and
https://github.com/rocq-prover/rocq/issues/2986.
And marking [Pmap] consumers as [simpl never] does not work either, see:
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/171#note_53216 *)
Global Opaque Pmap_empty.

(** [partial_alter] is [set] or [remove], depending on the result of [f]. This
traverses the trie twice (once for [get], once for [set]/[remove]); std++'s
own version did it once. The outer [match] on the map comes first so that
[simpl] does not unfold the operation on the opaque [∅], as before. *)
Local Definition Pmap_partial_alter_def {A} (f : option A → option A)
    (i : positive) (mt : Pmap A) : Pmap A :=
  match mt with
  | PEmpty => match f None with Some x => PNodes (singleton i x) | None => PEmpty end
  | PNodes t =>
     match f (Trie.get' t i) with Some x => set i x (PNodes t) | None => remove i (PNodes t) end
  end.
Global Instance Pmap_partial_alter {A} : PartialAlter positive A (Pmap A) :=
  Pmap_partial_alter_def.
Local Lemma Pmap_partial_alter_set_remove {A} (f : option A → option A) i (mt : Pmap A) :
  partial_alter f i mt =
    match f (get i mt) with Some x => set i x mt | None => remove i mt end.
Proof. by destruct mt. Qed.

Global Instance Pmap_fmap : FMap Pmap := λ {A B} f mt, map_filter (λ x, Some (f x)) mt.
Global Instance Pmap_omap : OMap Pmap := λ {A B} f mt, map_filter f mt.
Global Instance Pmap_merge : Merge Pmap := λ {A B C} f mt1 mt2,
  combine (diag_None f) mt1 mt2.

Local Definition Pmap_fold_aux {A B} (go : positive → B → Pmap_ne A → B)
    (i : positive) (y : B) (mt : Pmap A) : B :=
  match mt with PEmpty => y | PNodes t => go i y t end.
Local Definition Pmap_ne_fold {A B} (f : positive → A → B → B) :
    positive → B → Pmap_ne A → B :=
  fix go i y t :=
    Pmap_ne_case t $ λ ml mx mr,
      Pmap_fold_aux go i~1
        (Pmap_fold_aux go i~0
          match mx with None => y | Some x => f (Pos.reverse i) x y end ml) mr.
Global Instance Pmap_fold {A} : MapFold positive A (Pmap A) := λ {B} f,
  Pmap_fold_aux (Pmap_ne_fold f) 1.

(** Proofs *)
Local Definition PNode_valid {A} (ml : Pmap A) (mx : option A) (mr : Pmap A) :=
  isBranch ml mx mr.
Local Lemma Pmap_ind {A} (P : Pmap A → Prop) :
  P PEmpty →
  (∀ ml mx mr, PNode_valid ml mx mr → P ml → P mr → P (PNode ml mx mr)) →
  ∀ mt, P mt.
Proof. intros Hemp Hnode. apply trie_ind; [done|]. intros. by apply (Hnode l o r). Qed.

Local Lemma Pmap_lookup_PNode {A} (ml mr : Pmap A) mx i :
  PNode ml mx mr !! i = match i with 1 => mx | i~0 => ml !! i | i~1 => mr !! i end.
Proof. apply get_Node. Qed.
Local Lemma PNode_Node {A} (ml : Pmap A) mx mr : PNode ml mx mr = Node ml mx mr.
Proof. done. Qed.

Local Lemma Pmap_eq {A} (mt1 mt2 : Pmap A) : (∀ i, mt1 !! i = mt2 !! i) → mt1 = mt2.
Proof. apply extensionality. Qed.

Local Lemma Pmap_insert_set {A} i (x : A) (mt : Pmap A) : <[i:=x]> mt = set i x mt.
Proof. by destruct mt. Qed.
Local Lemma Pmap_delete_remove {A} i (mt : Pmap A) : delete i mt = remove i mt.
Proof. by destruct mt. Qed.

Local Lemma Pmap_partial_alter_PNode {A} (f : option A → option A) i ml mx mr :
  partial_alter f i (PNode ml mx mr) =
    match i with
    | 1 => PNode ml (f mx) mr
    | i~0 => PNode (partial_alter f i ml) mx mr
    | i~1 => PNode ml mx (partial_alter f i mr)
    end.
Proof.
  rewrite Pmap_partial_alter_set_remove. unfold PNode. rewrite get_Node.
  destruct i; rewrite ?Pmap_partial_alter_set_remove; destruct (f _);
    by rewrite ?set_Node, ?remove_Node.
Qed.
Local Lemma Pmap_lookup_partial_alter_eq {A} (f : option A → option A)
    (mt : Pmap A) i :
  partial_alter f i mt !! i = f (mt !! i).
Proof.
  rewrite Pmap_partial_alter_set_remove. unfold lookup, Pmap_lookup.
  destruct (f (get i mt)) eqn:?; [apply get_set_same|apply get_remove_same].
Qed.
Local Lemma Pmap_lookup_partial_alter_ne {A} (f : option A → option A)
    (mt : Pmap A) i j :
  i ≠ j → partial_alter f i mt !! j = mt !! j.
Proof.
  intros. rewrite Pmap_partial_alter_set_remove. unfold lookup, Pmap_lookup.
  destruct (f (get i mt)); [apply get_set_diff|apply get_remove_diff]; done.
Qed.

Local Lemma Pmap_fmap_PNode {A B} (f : A → B) ml mx mr :
  f <$> PNode ml mx mr = PNode (f <$> ml) (f <$> mx) (f <$> mr).
Proof.
  unfold fmap at 1 3 4, Pmap_fmap, PNode. rewrite map_filter_Node. by destruct mx.
Qed.
Local Lemma Pmap_lookup_fmap {A B} (f : A → B) (mt : Pmap A) i :
  (f <$> mt) !! i = f <$> mt !! i.
Proof.
  unfold fmap at 1, Pmap_fmap, lookup, Pmap_lookup. rewrite get_map_filter.
  by destruct (get i mt).
Qed.

Local Lemma Pmap_omap_PNode {A B} (f : A → option B) ml mx mr :
  omap f (PNode ml mx mr) = PNode (omap f ml) (mx ≫= f) (omap f mr).
Proof. unfold omap, Pmap_omap, PNode. rewrite map_filter_Node. by destruct mx. Qed.
Local Lemma Pmap_lookup_omap {A B} (f : A → option B) (mt : Pmap A) i :
  omap f mt !! i = mt !! i ≫= f.
Proof.
  unfold omap, Pmap_omap, lookup, Pmap_lookup. rewrite get_map_filter.
  by destruct (get i mt).
Qed.

Local Lemma Pmap_lookup_merge {A B C} (f : option A → option B → option C)
    (mt1 : Pmap A) (mt2 : Pmap B) i :
  merge f mt1 mt2 !! i = diag_None f (mt1 !! i) (mt2 !! i).
Proof. apply get_combine. done. Qed.

Section Pmap_fold.
  Local Notation Pmap_fold f := (Pmap_fold_aux (Pmap_ne_fold f)).

  Local Lemma Pmap_fold_PNode {A B} (f : positive → A → B → B) i y ml mx mr :
    Pmap_fold f i y (PNode ml mx mr) = Pmap_fold f i~1
      (Pmap_fold f i~0
        match mx with None => y | Some x => f (Pos.reverse i) x y end ml) mr.
  Proof. unfold PNode. by destruct ml, mx, mr. Qed.

  Local Lemma Pmap_fold_ind {A} (P : Pmap A → Prop) :
    P PEmpty →
    (∀ i x mt,
      mt !! i = None →
      (∀ j A' B (f : positive → A' → B → B) (g : A → A') b x',
        Pmap_fold f j b (<[i:=x']> (g <$> mt))
        = f (Pos.reverse_go i j) x' (Pmap_fold f j b (g <$> mt))) →
      P mt → P (<[i:=x]> mt)) →
    ∀ mt, P mt.
  Proof.
    intros Hemp Hinsert mt. revert P Hemp Hinsert.
    induction mt as [|ml mx mr ? IHl IHr] using Pmap_ind;
      intros P Hemp Hinsert; [done|].
    apply (IHr (λ mt, P (PNode ml mx mt))).
    { apply (IHl (λ mt, P (PNode mt mx PEmpty))).
      { destruct mx as [x|]; [|done].
        replace (PNode PEmpty (Some x) PEmpty)
          with (<[1:=x]> (PEmpty : Pmap A)) by done.
        by apply Hinsert. }
      intros i x mt ? Hfold ?.
      replace (PNode (<[i:=x]> mt) mx PEmpty)
        with (<[i~0:=x]> (PNode mt mx (PEmpty : Pmap A)))
        by (by rewrite !Pmap_insert_set, !PNode_Node, set_Node).
      apply Hinsert.
      - by rewrite Pmap_lookup_PNode.
      - intros j A' B f g b x'.
        replace (<[i~0:=x']> (g <$> PNode mt mx (PEmpty : Pmap A)))
          with (PNode (<[i:=x']> (g <$> mt)) (g <$> mx) (PEmpty : Pmap A'))
          by (by rewrite !Pmap_insert_set, Pmap_fmap_PNode, !PNode_Node, set_Node).
        replace (g <$> PNode mt mx (PEmpty : Pmap A))
          with (PNode (g <$> mt) (g <$> mx) (PEmpty : Pmap A')) by (by rewrite Pmap_fmap_PNode).
        rewrite !Pmap_fold_PNode; cbn [Pmap_fold_aux Pos.reverse_go]; auto.
      - done. }
    intros i x mt r ? Hfold.
    replace (PNode ml mx (<[i:=x]> mt))
      with (<[i~1:=x]> (PNode ml mx mt)) by (by rewrite !Pmap_insert_set, !PNode_Node, set_Node).
    apply Hinsert.
    - by rewrite Pmap_lookup_PNode.
    - intros j A' B f g b x'.
      replace (<[i~1:=x']> (g <$> PNode ml mx mt))
        with (PNode (g <$> ml) (g <$> mx) (<[i:=x']> (g <$> mt)))
        by (by rewrite !Pmap_insert_set, Pmap_fmap_PNode, !PNode_Node, set_Node).
      replace (g <$> PNode ml mx mt)
        with (PNode (g <$> ml) (g <$> mx) (g <$> mt)) by (by rewrite Pmap_fmap_PNode).
      rewrite !Pmap_fold_PNode; cbn [Pmap_fold_aux Pos.reverse_go]; auto.
    - done.
  Qed.
End Pmap_fold.

(** Instance of the finite map type class *)
Global Instance Pmap_finmap : FinMap positive Pmap.
Proof.
  split.
  - intros. by apply Pmap_eq.
  - done.
  - intros. apply Pmap_lookup_partial_alter_eq.
  - intros. by apply Pmap_lookup_partial_alter_ne.
  - intros. apply Pmap_lookup_fmap.
  - intros. apply Pmap_lookup_omap.
  - intros. apply Pmap_lookup_merge.
  - done.
  - intros A P Hemp Hinsert. apply Pmap_fold_ind; [done|].
    intros i x mt ? Hfold. apply Hinsert; [done|]. apply (Hfold 1).
Qed.

Global Program Instance Pmap_countable `{Countable A} : Countable (Pmap A) :=
  map_countable.

(** * Finite sets *)
(** We construct sets of [positives]s satisfying extensional equality. *)
Notation Pset := (mapset Pmap).
Global Instance Pmap_dom {A} : Dom (Pmap A) Pset := mapset_dom.
Global Instance Pmap_dom_spec : FinMapDom positive Pmap Pset := mapset_dom_spec.
