(** This file is maintained by Michael Sammler. *)
From Stdlib Require Znumtheory.
From Stdlib Require Import ZifyNat.
From Stdlib Require Import Zmod Bits.
From stdpp Require Export numbers.
From stdpp Require Import countable finite.

(** * bitvector library *)
(** This file provides the [bv n] type for representing [n]-bit
integers with the standard operations. [bv n] is the Rocq standard
library type [bits (Z.of_N n)] (i.e. [Zmod (2 ^ Z.of_N n)]) and the
operations are aliases of, or thin wrappers around, the operations of
[Stdlib.Zmod]; see [ZMOD_PORT.md] for the list. It also provides the
[bv_saturate] tactic for learning facts about the range of bit vector
variables in context. More extensive automation can be found in
[bitvector_auto.v].

Additionally, this file provides the [bvn] type for representing a
bitvector of arbitrary size. *)

(** * Settings *)
Local Open Scope Z_scope.

(** * Preliminary definitions *)
Definition bv_modulus (n : N) : Z := 2 ^ (Z.of_N n).
Global Arguments bv_modulus : simpl never.
Definition bv_half_modulus (n : N) : Z := bv_modulus n `div` 2.
Definition bv_wrap (n : N) (z : Z) : Z := z `mod` bv_modulus n.
Definition bv_swrap (n : N) (z : Z) : Z := bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n.

Lemma bv_modulus_pos n :
  0 < bv_modulus n.
Proof. apply Z.pow_pos_nonneg; lia. Qed.
Lemma bv_modulus_gt_1 n :
  n ≠ 0%N →
  1 < bv_modulus n.
Proof. intros ?. apply Z.pow_gt_1; lia. Qed.
Lemma bv_half_modulus_nonneg n :
  0 ≤ bv_half_modulus n.
Proof. apply Z.div_pos; [|done]. pose proof bv_modulus_pos n. lia. Qed.

Lemma bv_modulus_add n1 n2 :
  bv_modulus (n1 + n2) = bv_modulus n1 * bv_modulus n2.
Proof. unfold bv_modulus. rewrite N2Z.inj_add. eapply Z.pow_add_r; lia. Qed.

Lemma bv_half_modulus_twice n:
  n ≠ 0%N →
  bv_half_modulus n + bv_half_modulus n = bv_modulus n.
Proof.
  intros. unfold bv_half_modulus, bv_modulus.
  rewrite Z.add_diag. symmetry. apply Z_div_exact_2; [lia|].
  rewrite <-Z.pow_pred_r by lia. rewrite Z.mul_comm. by apply Z.mod_mul.
Qed.

Lemma bv_half_modulus_lt_modulus n:
  bv_half_modulus n < bv_modulus n.
Proof.
  pose proof bv_modulus_pos n.
  apply Z_div_lt; [done| lia].
Qed.

Lemma bv_modulus_le_mono n m:
  (n ≤ m)%N →
  bv_modulus n ≤ bv_modulus m.
Proof. intros. apply Z.pow_le_mono; [done|lia]. Qed.
Lemma bv_half_modulus_le_mono n m:
  (n ≤ m)%N →
  bv_half_modulus n ≤ bv_half_modulus m.
Proof. intros. apply Z.div_le_mono; [done|]. by apply bv_modulus_le_mono. Qed.

Lemma bv_modulus_0:
  bv_modulus 0 = 1.
Proof. done. Qed.
Lemma bv_half_modulus_0:
  bv_half_modulus 0 = 0.
Proof. done. Qed.

Lemma bv_half_modulus_twice_mult n:
  bv_half_modulus n + bv_half_modulus n = (Z.of_N n `min` 1) * bv_modulus n.
Proof. destruct (decide (n = 0%N)); subst; [ rewrite bv_half_modulus_0 | rewrite bv_half_modulus_twice]; lia. Qed.

Lemma bv_wrap_in_range n z:
  0 ≤ bv_wrap n z < bv_modulus n.
Proof. apply Z.mod_pos_bound. apply bv_modulus_pos. Qed.

Lemma bv_swrap_in_range n z:
  n ≠ 0%N →
  - bv_half_modulus n ≤ bv_swrap n z < bv_half_modulus n.
Proof.
  intros ?. unfold bv_swrap.
  pose proof bv_half_modulus_twice n.
  pose proof bv_wrap_in_range n (z + bv_half_modulus n).
  lia.
Qed.

Lemma bv_wrap_small n z :
  0 ≤ z < bv_modulus n → bv_wrap n z = z.
Proof. intros. by apply Z.mod_small. Qed.

Lemma bv_swrap_small n z :
  - bv_half_modulus n ≤ z < bv_half_modulus n →
  bv_swrap n z = z.
Proof.
  intros Hrange. unfold bv_swrap.
  destruct (decide (n = 0%N)); subst.
  { rewrite bv_half_modulus_0 in Hrange. lia. }
  pose proof bv_half_modulus_twice n.
  rewrite bv_wrap_small by lia. lia.
Qed.

Lemma bv_wrap_0 n :
  bv_wrap n 0 = 0.
Proof. done. Qed.
Lemma bv_swrap_0 n :
  bv_swrap n 0 = 0.
Proof.
  pose proof bv_half_modulus_lt_modulus n.
  pose proof bv_half_modulus_nonneg n.
  unfold bv_swrap. rewrite bv_wrap_small; lia.
Qed.

Lemma bv_wrap_idemp n b : bv_wrap n (bv_wrap n b) = bv_wrap n b.
Proof. unfold bv_wrap. by rewrite Zmod_mod. Qed.

Definition bv_wrap_factor (n : N) (x z : Z) :=
  x = - z `div` bv_modulus n.

Lemma bv_wrap_factor_intro n z :
  ∃ x, bv_wrap_factor n x z ∧ bv_wrap n z = z + x * bv_modulus n.
Proof.
  eexists _. split; [done|].
  pose proof (bv_modulus_pos n). unfold bv_wrap. rewrite Z.mod_eq; lia.
Qed.

Lemma bv_wrap_add_modulus c n z:
  bv_wrap n (z + c * bv_modulus n) = bv_wrap n z.
Proof. apply Z_mod_plus_full. Qed.
Lemma bv_wrap_add_modulus_1 n z:
  bv_wrap n (z + bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus 1 n z). f_equal. lia. Qed.
Lemma bv_wrap_sub_modulus c n z:
  bv_wrap n (z - c * bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus (-c) n z). f_equal. lia. Qed.
Lemma bv_wrap_sub_modulus_1 n z:
  bv_wrap n (z - bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus (-1) n z). done. Qed.

Lemma bv_wrap_add_idemp n x y :
  bv_wrap n (bv_wrap n x + bv_wrap n y) = bv_wrap n (x + y).
Proof. symmetry. apply Zplus_mod. Qed.
Lemma bv_wrap_add_idemp_l n x y :
  bv_wrap n (bv_wrap n x + y) = bv_wrap n (x + y).
Proof. apply Zplus_mod_idemp_l. Qed.
Lemma bv_wrap_add_idemp_r n x y :
  bv_wrap n (x + bv_wrap n y) = bv_wrap n (x + y).
Proof. apply Zplus_mod_idemp_r. Qed.

Lemma bv_wrap_opp_idemp n x :
  bv_wrap n (- bv_wrap n x) = bv_wrap n (- x).
Proof.
  unfold bv_wrap. pose proof (bv_modulus_pos n).
  destruct (decide (x `mod` bv_modulus n = 0)) as [Hx|Hx].
  - rewrite !Z.mod_opp_l_z; [done |lia|done|lia|by rewrite Hx].
  - rewrite !Z.mod_opp_l_nz, Z.mod_mod;
      [done|lia|lia|done|lia|by rewrite Z.mod_mod by lia].
Qed.

Lemma bv_wrap_mul_idemp n x y :
  bv_wrap n (bv_wrap n x * bv_wrap n y) = bv_wrap n (x * y).
Proof. etrans; [| apply Zmult_mod_idemp_r]. apply Zmult_mod_idemp_l. Qed.
Lemma bv_wrap_mul_idemp_l n x y :
  bv_wrap n (bv_wrap n x * y) = bv_wrap n (x * y).
Proof. apply Zmult_mod_idemp_l. Qed.
Lemma bv_wrap_mul_idemp_r n x y :
  bv_wrap n (x * bv_wrap n y) = bv_wrap n (x * y).
Proof. apply Zmult_mod_idemp_r. Qed.

Lemma bv_wrap_sub_idemp n x y :
  bv_wrap n (bv_wrap n x - bv_wrap n y) = bv_wrap n (x - y).
Proof.
  by rewrite <-!Z.add_opp_r, <-bv_wrap_add_idemp_r,
    bv_wrap_opp_idemp, bv_wrap_add_idemp.
 Qed.
Lemma bv_wrap_sub_idemp_l n x y :
  bv_wrap n (bv_wrap n x - y) = bv_wrap n (x - y).
Proof. by rewrite <-!Z.add_opp_r, bv_wrap_add_idemp_l. Qed.
Lemma bv_wrap_sub_idemp_r n x y :
  bv_wrap n (x - bv_wrap n y) = bv_wrap n (x - y).
Proof.
  by rewrite <-!Z.add_opp_r, <-bv_wrap_add_idemp_r,
    bv_wrap_opp_idemp, bv_wrap_add_idemp_r.
Qed.

Lemma bv_wrap_succ_idemp n x :
  bv_wrap n (Z.succ (bv_wrap n x)) = bv_wrap n (Z.succ x).
Proof. by rewrite <-!Z.add_1_r, bv_wrap_add_idemp_l. Qed.
Lemma bv_wrap_pred_idemp n x :
  bv_wrap n (Z.pred (bv_wrap n x)) = bv_wrap n (Z.pred x).
Proof. by rewrite <-!Z.sub_1_r, bv_wrap_sub_idemp_l. Qed.

Lemma bv_wrap_add_inj n x1 x2 y :
  bv_wrap n x1 = bv_wrap n x2 ↔ bv_wrap n (x1 + y) = bv_wrap n (x2 + y).
Proof.
  split; intros Heq.
  - by rewrite <-bv_wrap_add_idemp_l, Heq, bv_wrap_add_idemp_l.
  - pose proof (bv_wrap_factor_intro n (x1 + y)) as [f1[? Hx1]].
    pose proof (bv_wrap_factor_intro n (x2 + y)) as [f2[? Hx2]].
    assert (x1 = x2 + f2 * bv_modulus n - f1 * bv_modulus n) as -> by lia.
    by rewrite bv_wrap_sub_modulus, bv_wrap_add_modulus.
Qed.

Lemma bv_swrap_wrap n z:
  bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof. unfold bv_swrap, bv_wrap. by rewrite Zplus_mod_idemp_l. Qed.

Lemma bv_wrap_modulo n z :
  bv_wrap n z = z `mod` 2 ^ Z.of_N n.
Proof. done. Qed.
Lemma bv_swrap_smodulo n z :
  bv_swrap n z = Z.smodulo z (bv_modulus n).
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, Z.smodulo, Z.omodulo.
  pose proof bv_modulus_pos n.
  rewrite Z.quot_div_nonneg, Z.sub_opp_r by lia. lia.
Qed.

Lemma bv_wrap_bv_wrap n1 n2 bv :
  (n1 ≤ n2)%N →
  bv_wrap n1 (bv_wrap n2 bv) = bv_wrap n1 bv.
Proof.
  intros ?. unfold bv_wrap.
  rewrite <-Znumtheory.Zmod_div_mod; [done| apply bv_modulus_pos.. |].
  unfold bv_modulus. eexists (2 ^ (Z.of_N n2 - Z.of_N n1)).
  rewrite <-Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bv_wrap_land n z :
  bv_wrap n z = Z.land z (Z.ones (Z.of_N n)).
Proof. by rewrite Z.land_ones by lia. Qed.
Lemma bv_wrap_spec n z i:
  0 ≤ i →
  Z.testbit (bv_wrap n z) i = bool_decide (i < Z.of_N n) && Z.testbit z i.
Proof.
  intros ?. rewrite bv_wrap_land, Z.land_spec, Z.ones_spec by lia.
  case_bool_decide; simpl; by rewrite ?andb_true_r, ?andb_false_r.
Qed.
Lemma bv_wrap_spec_low n z i:
  0 ≤ i < Z.of_N n →
  Z.testbit (bv_wrap n z) i = Z.testbit z i.
Proof. intros ?. rewrite bv_wrap_spec; [|lia]. case_bool_decide; [done|]. lia. Qed.
Lemma bv_wrap_spec_high n z i:
  Z.of_N n ≤ i →
  Z.testbit (bv_wrap n z) i = false.
Proof. intros ?. rewrite bv_wrap_spec; [|lia]. case_bool_decide; [|done]. lia. Qed.

Lemma bv_swrap_spec n (z i : Z):
  0 ≤ i →
  Z.testbit (bv_swrap n z) i =
    if bool_decide (i < Z.of_N n-1) then
      Z.testbit z i
    else
      Z.testbit z (Z.of_N n-1).
Proof.
  destruct (decide (0 < n)%N).
  - intros ?.
    unfold bv_swrap, bv_half_modulus, bv_modulus.
    replace (2 ^ Z.of_N n `div` 2) with (2 ^ (Z.of_N n - 1)). 2: {
      rewrite Z.pow_sub_r; lia.
    }
    case_bool_decide as Hi.
    + rewrite Z.sub_pow2_spec_low, bv_wrap_spec_low,
        Z.add_pow2_spec_low by lia.
      done.
    + destruct (decide (i = Z.of_N n - 1)) as [-> | Ineq].
      * rewrite Z.sub_pow2_spec_top, bv_wrap_spec_low, Z.add_pow2_spec_top by lia.
        by apply negb_involutive.
      * rewrite Z.sub_pow2_spec_high; [ | lia | | lia ]. 2: {
          replace (Z.succ (Z.of_N n - 1)) with (Z.of_N n) by lia.
          apply bv_wrap_in_range.
        }
        rewrite bv_wrap_spec_low by lia.
        rewrite Z.add_pow2_spec_top by lia.
        by apply negb_involutive.
  - intros ?.
    replace n with 0%N by lia.
    rewrite bool_decide_eq_false_2 by lia.
    unfold bv_swrap.
    rewrite bv_half_modulus_0, Z.add_0_r, Z.sub_0_r.
    unfold bv_wrap.
    change (bv_modulus 0) with 1.
    by rewrite Z.mod_1_r, Z.bits_0, Z.testbit_neg_r.
Qed.

(** * [BvWf] *)
(** The [BvWf] typeclass checks that the integer [z] can be
interpreted as a [n]-bit integer. [BvWf] is a typeclass such that it
can be automatically inferred for bitvector constants. *)
Class BvWf (n : N) (z : Z) : Prop :=
    bv_wf : (0 <=? z) && (z <? bv_modulus n)
.
Global Hint Mode BvWf + + : typeclass_instances.
Global Instance bv_wf_pi n z : ProofIrrel (BvWf n z).
Proof. unfold BvWf. apply _. Qed.
Global Instance bv_wf_dec n z : Decision (BvWf n z).
Proof. unfold BvWf. apply _. Defined.

Global Typeclasses Opaque BvWf.

Ltac solve_BvWf :=
  lazymatch goal with
    |- BvWf ?n ?v =>
      is_closed_term n;
      is_closed_term v;
      try (vm_compute; exact I);
      fail "Bitvector constant" v "does not fit into" n "bits"
  end.
Global Hint Extern 10 (BvWf _ _) => solve_BvWf : typeclass_instances.

Lemma bv_wf_in_range n z:
  BvWf n z ↔ 0 ≤ z < bv_modulus n.
Proof. unfold BvWf. by rewrite andb_True, !Is_true_true, Z.leb_le, Z.ltb_lt. Qed.

Lemma bv_wrap_wf n z :
  BvWf n (bv_wrap n z).
Proof. apply bv_wf_in_range. apply bv_wrap_in_range. Qed.

Lemma bv_wf_bitwise_op {n} op bop n1 n2 :
  (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
  (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
  bop false false = false →
  BvWf n n1 →
  BvWf n n2 →
  BvWf n (op n1 n2).
Proof.
  intros Hbits Hnonneg Hop [? Hok1]%bv_wf_in_range [? Hok2]%bv_wf_in_range. apply bv_wf_in_range.
  split; [lia|].
  apply Z.bounded_iff_bits_nonneg; [lia..|]. intros l ?.
  eapply Z.bounded_iff_bits_nonneg in Hok1;[|try done; lia..].
  eapply Z.bounded_iff_bits_nonneg in Hok2;[|try done; lia..].
  by rewrite Hbits, Hok1, Hok2.
Qed.

(** * Definition of [bv n] *)
(** [bv n] is the standard library type [bits (Z.of_N n)], i.e.
[Zmod (2 ^ Z.of_N n)]. [BV n z] builds a bitvector from an integer [z]
that is known (via [BvWf]) to be in range; [bv_unsigned] and
[bv_signed] are thin wrappers around [Zmod.unsigned] and the
signed interpretation. *)
(** [bv n] is literally the standard library's [bits (Z.of_N n)], so the
hidden modulus of every operation is [2 ^ Z.of_N n]. *)
Definition bv (n : N) : Set := bits (Z.of_N n).

Definition BV (n : N) (z : Z) {H : BvWf n z} : bv n :=
  Zmod.of_small_Z (bv_modulus n) z.
Global Arguments BV _ _ {_}.
Global Arguments BV : simpl never.

Definition bv_unsigned {n} (b : bv n) : Z := Zmod.unsigned b.
Global Arguments bv_unsigned : simpl never.

Definition bv_signed {n} (b : bv n) := bv_swrap n (bv_unsigned b).

Lemma bv_unsigned_BV n z Hwf:
  bv_unsigned (@BV n z Hwf) = z.
Proof.
  unfold bv_unsigned, BV. apply Zmod.unsigned_of_small_Z.
  apply Z.mod_small, bv_wf_in_range, Hwf.
Qed.

Lemma bv_signed_BV n z Hwf:
  bv_signed (@BV n z Hwf) = bv_swrap n z.
Proof. unfold bv_signed. by rewrite bv_unsigned_BV. Qed.

Lemma bv_unsigned_in_range n (b : bv n):
  0 ≤ bv_unsigned b < bv_modulus n.
Proof. unfold bv_unsigned. apply Zmod.unsigned_pos_bound, bv_modulus_pos. Qed.

(** [bv_is_wf] used to be the second field of the [bv] record. *)
Lemma bv_is_wf {n} (b : bv n) : BvWf n (bv_unsigned b).
Proof. apply bv_wf_in_range, bv_unsigned_in_range. Qed.

Lemma bv_signed_Zmod_signed n (b : bv n) :
  bv_signed b = Zmod.signed b.
Proof. unfold bv_signed, bv_unsigned. rewrite bv_swrap_smodulo. apply Zmod.smod_unsigned. Qed.

Lemma bv_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ bv_unsigned b1 = bv_unsigned b2.
Proof. unfold bv_unsigned. symmetry. apply Zmod.unsigned_inj_iff. Qed.

Lemma bv_neq n (b1 b2 : bv n) :
  b1 ≠ b2 ↔ bv_unsigned b1 ≠ bv_unsigned b2.
Proof. unfold not. by rewrite bv_eq. Qed.

Global Instance bv_unsigned_inj n : Inj (=) (=) (@bv_unsigned n).
Proof. intros ???. by apply bv_eq. Qed.

(** [bv] used to be a record with constructor [BV], so [destruct b] and
[induction b] gave a [z : Z] and a [BvWf n z]. These eliminators give the
same shape: [destruct b as [z Hwf] using bv_rect] (or [using bv_ind]). *)
Lemma bv_BV_unsigned n (b : bv n) : @BV n (bv_unsigned b) (bv_is_wf b) = b.
Proof. apply bv_eq. apply bv_unsigned_BV. Qed.

Definition bv_rect {n} (P : bv n → Type)
    (f : ∀ z (Hwf : BvWf n z), P (@BV n z Hwf)) (b : bv n) : P b :=
  eq_rect _ P (f (bv_unsigned b) (bv_is_wf b)) _ (bv_BV_unsigned n b).
Definition bv_rec {n} (P : bv n → Set) := @bv_rect n P.
Definition bv_ind {n} (P : bv n → Prop) := @bv_rect n P.

Definition Z_to_bv_checked (n : N) (z : Z) : option (bv n) :=
  H ← guard (BvWf n z); Some (@BV n z H).

Definition Z_to_bv (n : N) (z : Z) : bv n := Zmod.of_Z (bv_modulus n) z.

Lemma Z_to_bv_unsigned n z:
  bv_unsigned (Z_to_bv n z) = bv_wrap n z.
Proof. unfold bv_unsigned, Z_to_bv, bv_wrap. apply Zmod.unsigned_of_Z. Qed.

Lemma Z_to_bv_signed n z:
  bv_signed (Z_to_bv n z) = bv_swrap n z.
Proof. unfold bv_signed. rewrite Z_to_bv_unsigned. apply bv_swrap_wrap. Qed.

Lemma Z_to_bv_small n z:
  0 ≤ z < bv_modulus n →
  bv_unsigned (Z_to_bv n z) = z.
Proof. rewrite Z_to_bv_unsigned. apply bv_wrap_small. Qed.

Lemma bv_wrap_bv_unsigned n (b : bv n):
  bv_wrap n (bv_unsigned b) = bv_unsigned b.
Proof. rewrite bv_wrap_small; [done|apply bv_unsigned_in_range]. Qed.

Lemma Z_to_bv_bv_unsigned n (b : bv n):
  Z_to_bv n (bv_unsigned b) = b.
Proof. apply bv_eq. by rewrite Z_to_bv_unsigned, bv_wrap_bv_unsigned. Qed.

Lemma bv_eq_wrap n (b1 b2 : bv n) :
  b1 = b2 ↔ bv_wrap n (bv_unsigned b1) = bv_wrap n (bv_unsigned b2).
Proof.
  rewrite !bv_wrap_small; [apply bv_eq | apply bv_unsigned_in_range..].
Qed.

Lemma bv_neq_wrap n (b1 b2 : bv n) :
  b1 ≠ b2 ↔ bv_wrap n (bv_unsigned b1) ≠ bv_wrap n (bv_unsigned b2).
Proof. unfold not. by rewrite bv_eq_wrap. Qed.

Lemma bv_eq_signed n (b1 b2 : bv n) :
  b1 = b2 ↔ bv_signed b1 = bv_signed b2.
Proof.
  split; [naive_solver |].
  unfold bv_signed, bv_swrap. intros ?.
  assert (bv_wrap n (bv_unsigned b1 + bv_half_modulus n)
          = bv_wrap n (bv_unsigned b2 + bv_half_modulus n)) as ?%bv_wrap_add_inj by lia.
  by apply bv_eq_wrap.
Qed.

Lemma bv_signed_in_range n (b : bv n):
  n ≠ 0%N →
  - bv_half_modulus n ≤ bv_signed b < bv_half_modulus n.
Proof. apply bv_swrap_in_range. Qed.

Lemma bv_unsigned_spec_high i n (b : bv n) :
  Z.of_N n ≤ i →
  Z.testbit (bv_unsigned b) i = false.
Proof.
  intros ?. pose proof (bv_unsigned_in_range _ b). unfold bv_modulus in *.
  eapply Z.bounded_iff_bits_nonneg; [..|done]; lia.
Qed.

Lemma bv_unsigned_N_0 (b : bv 0):
  bv_unsigned b = 0.
Proof.
  pose proof bv_unsigned_in_range 0 b as H.
  rewrite bv_modulus_0 in H. lia.
Qed.
Lemma bv_signed_N_0 (b : bv 0):
  bv_signed b = 0.
Proof. unfold bv_signed. by rewrite bv_unsigned_N_0, bv_swrap_0. Qed.

Lemma bv_swrap_bv_signed n (b : bv n):
  bv_swrap n (bv_signed b) = bv_signed b.
Proof.
  destruct (decide (n = 0%N)); subst.
  { by rewrite bv_signed_N_0, bv_swrap_0. }
  apply bv_swrap_small. by apply bv_signed_in_range.
Qed.

Lemma Z_to_bv_checked_bv_unsigned n (b : bv n):
  Z_to_bv_checked n (bv_unsigned b) = Some b.
Proof.
  unfold Z_to_bv_checked. case_guard; simplify_option_eq.
  - f_equal. apply bv_eq. by rewrite bv_unsigned_BV.
  - by pose proof bv_is_wf b.
Qed.
Lemma Z_to_bv_checked_Some n a (b : bv n):
  Z_to_bv_checked n a = Some b ↔ a = bv_unsigned b.
Proof.
  split.
  - unfold Z_to_bv_checked. case_guard; [|done]. intros ?. simplify_option_eq.
    by rewrite bv_unsigned_BV.
  - intros ->. apply Z_to_bv_checked_bv_unsigned.
Qed.

(** * Typeclass instances for [bv n] *)
Global Instance bv_eq_dec n : EqDecision (bv n) := λ b1 b2,
   match decide (bv_unsigned b1 = bv_unsigned b2) with
   | left eqv => left (Zmod.unsigned_inj _ b1 b2 eqv)
   | right eqv => right (λ eqb, eqv (f_equal bv_unsigned eqb))
   end.

Global Instance bv_countable n : Countable (bv n) :=
  inj_countable bv_unsigned (Z_to_bv_checked n) (Z_to_bv_checked_bv_unsigned n).

Global Program Instance bv_finite n : Finite (bv n) :=
  {| enum := Z_to_bv n <$> (seqZ 0 (bv_modulus n)) |}.
Next Obligation.
  intros n. apply NoDup_alt. intros i j x.
  rewrite !list_lookup_fmap.
  intros [? [[??]%lookup_seqZ ?]]%fmap_Some.
  intros [? [[??]%lookup_seqZ Hz]]%fmap_Some. subst.
  apply bv_eq in Hz. rewrite !Z_to_bv_small in Hz; lia.
Qed.
Next Obligation.
  intros n x. apply list_elem_of_lookup. eexists (Z.to_nat (bv_unsigned x)).
  rewrite list_lookup_fmap. apply fmap_Some. eexists _.
  pose proof (bv_unsigned_in_range _ x). split.
  - apply lookup_seqZ. split; [done|]. rewrite Z2Nat.id; lia.
  - apply bv_eq. rewrite Z_to_bv_small; rewrite Z2Nat.id; lia.
Qed.

Lemma bv_1_ind (P : bv 1 → Prop) :
  P (@BV 1 1 I) → P (@BV 1 0 I) → ∀ b : bv 1, P b.
Proof.
  intros ??. apply Forall_finite. repeat constructor.
  - by assert ((@BV 1 0 I) = (Z_to_bv 1 (Z.of_nat 0 + 0))) as <- by by apply bv_eq.
  - by assert ((@BV 1 1 I) = (Z_to_bv 1 (Z.of_nat 1 + 0))) as <- by by apply bv_eq.
Qed.

(** * [bv_saturate]: Add range facts about bit vectors to the context *)
Lemma bv_unsigned_in_range_alt n (b : bv n):
  -1 < bv_unsigned b < bv_modulus n.
Proof. pose proof (bv_unsigned_in_range _ b). lia. Qed.

Ltac bv_saturate :=
  repeat match goal with b : bv _ |- _ => first [
     clear b | (* Clear if unused *)
     (* We use [bv_unsigned_in_range_alt] instead of
     [bv_unsigned_in_range] since hypothesis of the form [0 ≤ ... < ...]
     can cause significant slowdowns in
     [Z.euclidean_division_equations_cleanup] due to
     https://github.com/rocq-prover/rocq/pull/17984 . *)
     learn_hyp (bv_unsigned_in_range_alt _ b) |
     learn_hyp (bv_signed_in_range _ b)
  ] end.

Ltac bv_saturate_unsigned :=
  repeat match goal with b : bv _ |- _ => first [
     clear b | (* Clear if unused *)
     (* See comment in [bv_saturate]. *)
     learn_hyp (bv_unsigned_in_range_alt _ b)
  ] end.

(** * Operations on [bv n] *)
Definition bv_0 (n : N) : bv n := Zmod.zero.
Global Instance bv_inhabited n : Inhabited (bv n) := populate (bv_0 n).

Definition bv_succ {n} (x : bv n) : bv n :=
  Z_to_bv n (Z.succ (bv_unsigned x)).
Definition bv_pred {n} (x : bv n) : bv n :=
  Z_to_bv n (Z.pred (bv_unsigned x)).

(** The operations whose meaning agrees with a [Zmod] operation and whose
arguments are only bitvectors are abbreviations of the [Zmod] operation, so
that [bv_add x y] and [Zmod.add x y] are the same term. The implicit
argument of these is the modulus [2 ^ Z.of_N n], not [n]: write
[@bv_add (2 ^ Z.of_N n)] instead of [@bv_add n]. *)
Abbreviation bv_add := Zmod.add. (* SMT: bvadd *)
Abbreviation bv_sub := Zmod.sub. (* SMT: bvsub *)
Abbreviation bv_opp := Zmod.opp. (* SMT: bvneg *)

Abbreviation bv_mul := Zmod.mul. (* SMT: bvmul *)
(** [bv_divu] differs from [Zmod.udiv] on division by zero: [bv_divu x 0 = 0]
(like [Z.div]) while [Zmod.udiv x 0 = -1]. See [bv_divu_udiv]. *)
Definition bv_divu {n} (x y : bv n) : bv n := (* SMT: bvudiv *)
  Z_to_bv n (Z.div (bv_unsigned x) (bv_unsigned y)).
Abbreviation bv_modu := Zmod.umod. (* SMT: bvurem *)
Definition bv_divs {n} (x y : bv n) : bv n :=
  Z_to_bv n (Z.div (bv_signed x) (bv_signed y)).
(** [bv_quots] differs from [Zmod.squot] on division by zero: [bv_quots x 0 = 0]
(like [Z.quot]) while [Zmod.squot x 0 = -1]. See [bv_quots_squot]. *)
Definition bv_quots {n} (x y : bv n) : bv n := (* SMT: bvsdiv *)
  Z_to_bv n (Z.quot (bv_signed x) (bv_signed y)).
Definition bv_mods {n} (x y : bv n) : bv n := (* SMT: bvsmod *)
  Z_to_bv n (Z.modulo (bv_signed x) (bv_signed y)).
Abbreviation bv_rems := Zmod.srem. (* SMT: bvsrem *)

Definition bv_shiftl {n} (x y : bv n) : bv n := (* SMT: bvshl *)
  Zmod.slu x (bv_unsigned y).
Definition bv_shiftr {n} (x y : bv n) : bv n := (* SMT: bvlshr *)
  Zmod.sru x (bv_unsigned y).
Definition bv_ashiftr {n} (x y : bv n) : bv n := (* SMT: bvashr *)
  Zmod.srs x (bv_unsigned y).

Abbreviation bv_or := Zmod.or. (* SMT: bvor *)
Abbreviation bv_and := Zmod.and. (* SMT: bvand *)
Abbreviation bv_xor := Zmod.xor. (* SMT: bvxor *)
Abbreviation bv_not := Zmod.not. (* SMT: bvnot *)

(** std++ made all bitvector operations opaque, so [simpl]/[cbn] never
unfolded them. An abbreviation cannot be made opaque without making the
[Zmod] operation opaque for everyone, so the [Zmod] operations are only
marked [simpl never] (a global setting as well, but a much weaker one). *)
Global Arguments Zmod.add : simpl never.
Global Arguments Zmod.sub : simpl never.
Global Arguments Zmod.opp : simpl never.
Global Arguments Zmod.mul : simpl never.
Global Arguments Zmod.umod : simpl never.
Global Arguments Zmod.srem : simpl never.
Global Arguments Zmod.or : simpl never.
Global Arguments Zmod.and : simpl never.
Global Arguments Zmod.xor : simpl never.
Global Arguments Zmod.not : simpl never.

(** std++ code writes [@bv_add n] with the width [n : N]; the explicit form
of the abbreviation is [@Zmod.add (bv_modulus n)]. These parsing-only
notations keep the std++ spelling: [@bv_add n] is [@Zmod.add (2 ^ Z.of_N n)].
They take precedence over [@bv_add m] with a modulus [m], and a bare
[@bv_add] without an argument does not parse. *)
Notation "'@' 'bv_add' n" := (@Zmod.add (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_sub' n" := (@Zmod.sub (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_opp' n" := (@Zmod.opp (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_mul' n" := (@Zmod.mul (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_modu' n" := (@Zmod.umod (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_rems' n" := (@Zmod.srem (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_or' n" := (@Zmod.or (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_and' n" := (@Zmod.and (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_xor' n" := (@Zmod.xor (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).
Notation "'@' 'bv_not' n" := (@Zmod.not (2 ^ Z.of_N n)) (at level 10, n at level 9, only parsing).

(* [bv_zero_extends z b] extends [b] to [z] bits with 0. If [z] is
smaller than [n], [b] is truncated. Note that [z] gives the resulting
size instead of the number of bits to add (as SMTLIB does) to avoid a
type-level [_ + _] *)
Definition bv_zero_extend {n} (z : N) (b : bv n) : bv z := (* SMT: zero_extend *)
  Zmod.firstn (Z.of_N z) b.

Definition bv_sign_extend {n} (z : N) (b : bv n) : bv z := (* SMT: sign_extend *)
  Z_to_bv z (bv_signed b).

(* s is start index and l is length. Note that this is different from
extract in SMTLIB which uses [extract (inclusive upper bound)
(inclusive lower bound)]. The version here is phrased in a way that
makes it impossible to use an upper bound that is lower than the lower
bound. *)
Definition bv_extract {n} (s l : N) (b : bv n) : bv l :=
  Z_to_bv l (bv_unsigned b ≫ Z.of_N s).

(* Note that we should always have n1 + n2 = n, but we use a parameter to avoid a type-level (_ + _) *)
(* [bv_concat] puts [b1] in the high bits; [Zmod.app] puts its first argument
in the low bits. See [bv_concat_app]. *)
Definition bv_concat n {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv n := (* SMT: concat *)
  Z_to_bv n (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).

Definition bv_to_little_endian m n (z : Z) : list (bv n) :=
  (λ b, Z_to_bv n b) <$> Z_to_little_endian m (Z.of_N n) z.

Definition little_endian_to_bv n (bs : list (bv n)) : Z :=
  little_endian_to_Z (Z.of_N n) (bv_unsigned <$> bs).

(** * Operations on [bv n] and Z *)
Definition bv_add_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.add (bv_unsigned x) y).
Definition bv_sub_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.sub (bv_unsigned x) y).
Definition bv_mul_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.mul (bv_unsigned x) y).

Definition bv_seq {n} (x : bv n) (len : Z) : list (bv n) :=
  (bv_add_Z x) <$> seqZ 0 len.

(** * Operations on [bv n] and bool *)
Definition bool_to_bv (n : N) (b : bool) : bv n :=
  Z_to_bv n (bool_to_Z b).

Definition bv_to_bits {n} (b : bv n) : list bool :=
  (λ i, Z.testbit (bv_unsigned b) i) <$> seqZ 0 (Z.of_N n).

(** * Notation for [bv] operations *)
Declare Scope bv_scope.
Delimit Scope bv_scope with bv.
Bind Scope bv_scope with bv.
(** The arguments of the abbreviated operations ([bv_add x y] is
[Zmod.add x y]) have type [Zmod _]. The standard library binds [Zmod_scope]
to [Zmod], but only in files that import [Stdlib.Zmod]; without this line
[bv_add x 5] or [bv_and (x ≪ 2) y] do not parse unless [bv_scope] is open.
[Bind Scope] is visible to files that import this one, so this binds
[bv_scope] to every [Zmod] argument there, including the ones of a plain
[Zmod m]. *)
Bind Scope bv_scope with Zmod.

Infix "+" := bv_add : bv_scope.
Infix "-" := bv_sub : bv_scope.
Notation "- x" := (bv_opp x) : bv_scope.
Infix "*" := bv_mul : bv_scope.
Infix "`divu`" := bv_divu (at level 35) : bv_scope.
Infix "`modu`" := bv_modu (at level 35) : bv_scope.
Infix "`divs`" := bv_divs (at level 35) : bv_scope.
Infix "`quots`" := bv_quots (at level 35) : bv_scope.
Infix "`mods`" := bv_mods (at level 35) : bv_scope.
Infix "`rems`" := bv_rems (at level 35) : bv_scope.
Infix "≪" := bv_shiftl : bv_scope.
Infix "≫" := bv_shiftr : bv_scope.
Infix "`ashiftr`" := bv_ashiftr (at level 35) : bv_scope.

Infix "`+Z`" := bv_add_Z (at level 50) : bv_scope.
Infix "`-Z`" := bv_sub_Z (at level 50) : bv_scope.
Infix "`*Z`" := bv_mul_Z (at level 40) : bv_scope.


(** This adds number notations into [bv_scope].
If the number literal is positive or 0, it gets expanded to [BV _ {num} _].
If the number literal is negative, it gets expanded as [Z_to_bv _ {num}].
In the negative case, the notation is parsing only and the [Z_to_bv] call will be
printed explicitly. *)
Inductive bv_number_notation := BVNumNonNeg (z : Z) | BVNumNeg (z : Z) | BVNumMk (z : Z).
Definition bv_number_notation_to_Z (n : bv_number_notation) : option Z :=
  match n with
  | BVNumNonNeg z => Some z
  (** Don't use the notation for negative numbers for printing. *)
  | BVNumNeg z => None
  (** [vm_compute] and friends normalize a bitvector to [Zmod.mk m z pf];
  print it as a number too. [Z_to_bv_number_notation] never produces
  [BVNumMk], so this is printing only. *)
  | BVNumMk z => Some z
  end.
Definition Z_to_bv_number_notation (z : Z) :=
  match z with
  | Zneg _ => BVNumNeg z
  | _ => BVNumNonNeg z
  end.

(** We need to temporarily change the implicit arguments of BV and
Z_to_bv such that we can pass them to [Number Notation]. *)
Local Arguments Z_to_bv {_} _.
Local Arguments BV {_} _ {_}.
Local Arguments ZmodDef.Zmod.mk {_} _ {_}.
(* [bv n] unfolds to [Zmod _], which the number notation machinery notices. *)
#[warnings="-via-type-remapping,-via-type-mismatch"]
Number Notation bv Z_to_bv_number_notation bv_number_notation_to_Z
  (via bv_number_notation mapping [[BV] => BVNumNonNeg, [Z_to_bv] => BVNumNeg,
                                   [ZmodDef.Zmod.mk] => BVNumMk]) : bv_scope.
Local Arguments BV _ _ {_}.
Local Arguments Z_to_bv : clear implicits.
Local Arguments ZmodDef.Zmod.mk : clear implicits.

(** * [bv_wrap_simplify]: typeclass-based automation for simplifying [bv_wrap] *)
(** The [bv_wrap_simplify] tactic removes [bv_wrap] where possible by
using the fact that [bv_wrap n (bv_warp n z) = bv_wrap n z]. The main
use case for this tactic is for proving the lemmas about the
operations of [bv n] below. Users should use the more extensive
automation provided by [bitvector_auto.v]. *)
Create HintDb bv_wrap_simplify_db discriminated.
Global Hint Constants Opaque : bv_wrap_simplify_db.
Global Hint Variables Opaque : bv_wrap_simplify_db.

Class BvWrapSimplify (n : N) (z z' : Z) := {
  bv_wrap_simplify_proof : bv_wrap n z = bv_wrap n z';
}.
Global Arguments bv_wrap_simplify_proof _ _ _ {_}.
Global Hint Mode BvWrapSimplify + + - : bv_wrap_simplify_db.

(** Default instance to end search. *)
Lemma bv_wrap_simplify_id n z :
  BvWrapSimplify n z z.
Proof. by constructor. Qed.
Global Hint Resolve bv_wrap_simplify_id | 1000 : bv_wrap_simplify_db.

(** [bv_wrap_simplify_bv_wrap] performs the actual simplification. *)
Lemma bv_wrap_simplify_bv_wrap n z z' :
  BvWrapSimplify n z z' →
  BvWrapSimplify n (bv_wrap n z) z'.
Proof. intros [->]. constructor. by rewrite bv_wrap_bv_wrap. Qed.
Global Hint Resolve bv_wrap_simplify_bv_wrap | 10 : bv_wrap_simplify_db.

(** The rest of the instances propagate [BvWrapSimplify].  *)
Lemma bv_wrap_simplify_succ n z z' :
  BvWrapSimplify n z z' →
  BvWrapSimplify n (Z.succ z) (Z.succ z').
Proof.
  intros [Hz]. constructor. by rewrite <-bv_wrap_succ_idemp, Hz, bv_wrap_succ_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_succ | 10 : bv_wrap_simplify_db.

Lemma bv_wrap_simplify_pred n z z' :
  BvWrapSimplify n z z' →
  BvWrapSimplify n (Z.pred z) (Z.pred z').
Proof.
  intros [Hz]. constructor. by rewrite <-bv_wrap_pred_idemp, Hz, bv_wrap_pred_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_pred | 10 : bv_wrap_simplify_db.

Lemma bv_wrap_simplify_opp n z z' :
  BvWrapSimplify n z z' →
  BvWrapSimplify n (- z) (- z').
Proof.
  intros [Hz]. constructor. by rewrite <-bv_wrap_opp_idemp, Hz, bv_wrap_opp_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_opp | 10 : bv_wrap_simplify_db.

Lemma bv_wrap_simplify_add n z1 z1' z2 z2' :
  BvWrapSimplify n z1 z1' →
  BvWrapSimplify n z2 z2' →
  BvWrapSimplify n (z1 + z2) (z1' + z2').
Proof.
  intros [Hz1] [Hz2]. constructor.
  by rewrite <-bv_wrap_add_idemp, Hz1, Hz2, bv_wrap_add_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_add | 10 : bv_wrap_simplify_db.

Lemma bv_wrap_simplify_sub n z1 z1' z2 z2' :
  BvWrapSimplify n z1 z1' →
  BvWrapSimplify n z2 z2' →
  BvWrapSimplify n (z1 - z2) (z1' - z2').
Proof.
  intros [Hz1] [Hz2]. constructor.
  by rewrite <-bv_wrap_sub_idemp, Hz1, Hz2, bv_wrap_sub_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_sub | 10 : bv_wrap_simplify_db.

Lemma bv_wrap_simplify_mul n z1 z1' z2 z2' :
  BvWrapSimplify n z1 z1' →
  BvWrapSimplify n z2 z2' →
  BvWrapSimplify n (z1 * z2) (z1' * z2').
Proof.
  intros [Hz1] [Hz2]. constructor.
  by rewrite <-bv_wrap_mul_idemp, Hz1, Hz2, bv_wrap_mul_idemp.
Qed.
Global Hint Resolve bv_wrap_simplify_mul | 10 : bv_wrap_simplify_db.

(** [bv_wrap_simplify_left] applies for goals of the form [bv_wrap n z1 = _] and
 tries to simplify them by removing any [bv_wrap] inside z1. *)
Ltac bv_wrap_simplify_left :=
  lazymatch goal with |- bv_wrap _ _ = _ => idtac end;
  etrans; [ notypeclasses refine (bv_wrap_simplify_proof _ _ _);
            typeclasses eauto with bv_wrap_simplify_db | ]
.

(** [bv_wrap_simplify] applies for goals of the form [bv_wrap n z1 = bv_wrap n z2] and
[bv_swrap n z1 = bv_swrap n z2] and tries to simplify them by removing any [bv_wrap]
and [bv_swrap] inside z1 and z2. *)
Ltac bv_wrap_simplify :=
  unfold bv_signed, bv_swrap;
  try match goal with | |- _ - _ = _ - _ => f_equal end;
  bv_wrap_simplify_left;
  symmetry;
  bv_wrap_simplify_left;
  symmetry.

Ltac bv_wrap_simplify_solve :=
  bv_wrap_simplify; f_equal; lia.


(** * Lemmas about [bv n] operations *)

(** ** Unfolding lemmas for the operations. *)
Lemma bv_signed_unsigned_wrap {n} (b : bv n) z :
  bv_unsigned b = bv_wrap n z →
  bv_signed b = bv_swrap n z.
Proof. unfold bv_signed. intros ->. apply bv_swrap_wrap. Qed.

Section unfolding.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_0_unsigned :
    bv_unsigned (bv_0 n) = 0.
  Proof. apply Zmod.unsigned_0. Qed.
  Lemma bv_0_signed :
    bv_signed (bv_0 n) = 0.
  Proof. unfold bv_signed. by rewrite bv_0_unsigned, bv_swrap_0. Qed.

  Lemma bv_succ_unsigned b :
    bv_unsigned (bv_succ b) = bv_wrap n (Z.succ (bv_unsigned b)).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_succ_signed b :
    bv_signed (bv_succ b) = bv_swrap n (Z.succ (bv_signed b)).
  Proof. unfold bv_succ. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_pred_unsigned b :
    bv_unsigned (bv_pred b) = bv_wrap n (Z.pred (bv_unsigned b)).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_pred_signed b :
    bv_signed (bv_pred b) = bv_swrap n (Z.pred (bv_signed b)).
  Proof. unfold bv_pred. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_add_unsigned b1 b2 :
    bv_unsigned (b1 + b2) = bv_wrap n (bv_unsigned b1 + bv_unsigned b2).
  Proof. apply Zmod.unsigned_add. Qed.
  Lemma bv_add_signed b1 b2 :
    bv_signed (b1 + b2) = bv_swrap n (bv_signed b1 + bv_signed b2).
  Proof. rewrite (bv_signed_unsigned_wrap _ _ (bv_add_unsigned _ _)). bv_wrap_simplify_solve. Qed.

  Lemma bv_sub_unsigned b1 b2 :
    bv_unsigned (b1 - b2) = bv_wrap n (bv_unsigned b1 - bv_unsigned b2).
  Proof. apply Zmod.unsigned_sub. Qed.
  Lemma bv_sub_signed b1 b2 :
    bv_signed (b1 - b2) = bv_swrap n (bv_signed b1 - bv_signed b2).
  Proof. rewrite (bv_signed_unsigned_wrap _ _ (bv_sub_unsigned _ _)). bv_wrap_simplify_solve. Qed.

  Lemma bv_opp_unsigned b :
    bv_unsigned (- b) = bv_wrap n (- bv_unsigned b).
  Proof. apply Zmod.unsigned_opp. Qed.
  Lemma bv_opp_signed b :
    bv_signed (- b) = bv_swrap n (- bv_signed b).
  Proof. rewrite (bv_signed_unsigned_wrap _ _ (bv_opp_unsigned _)). bv_wrap_simplify_solve. Qed.

  Lemma bv_mul_unsigned b1 b2 :
    bv_unsigned (b1 * b2) = bv_wrap n (bv_unsigned b1 * bv_unsigned b2).
  Proof. apply Zmod.unsigned_mul. Qed.
  Lemma bv_mul_signed b1 b2 :
    bv_signed (b1 * b2) = bv_swrap n (bv_signed b1 * bv_signed b2).
  Proof. rewrite (bv_signed_unsigned_wrap _ _ (bv_mul_unsigned _ _)). bv_wrap_simplify_solve. Qed.

  Lemma bv_divu_unsigned b1 b2 :
    bv_unsigned (b1 `divu` b2) = bv_unsigned b1 `div` bv_unsigned b2.
  Proof.
    unfold bv_divu. rewrite Z_to_bv_unsigned. apply bv_wrap_small. bv_saturate.
    destruct (decide (bv_unsigned b2 = 0)) as [->|?].
    { rewrite Z.div_0_r. lia. }
    split; [ apply Z.div_pos; lia |].
    apply (Z.le_lt_trans _ (bv_unsigned b1)); [|lia].
    apply Z.div_le_upper_bound; [ lia|]. nia.
  Qed.
  Lemma bv_divu_signed b1 b2 :
    bv_signed (b1 `divu` b2) = bv_swrap n (bv_unsigned b1 `div` bv_unsigned b2).
  Proof. unfold bv_signed. by rewrite bv_divu_unsigned. Qed.
  Lemma bv_divu_udiv b1 b2 :
    bv_unsigned b2 ≠ 0 →
    bv_divu b1 b2 = Zmod.udiv b1 b2.
  Proof.
    intros ?. apply bv_eq. rewrite bv_divu_unsigned. unfold bv_unsigned in *.
    symmetry. apply Zmod.unsigned_udiv_nonneg; [|done]. pose proof bv_modulus_pos n. lia.
  Qed.

  Lemma bv_modu_unsigned b1 b2 :
    bv_unsigned (b1 `modu` b2) = bv_unsigned b1 `mod` bv_unsigned b2.
  Proof. apply Zmod.unsigned_umod. Qed.
  Lemma bv_modu_signed b1 b2 :
    bv_signed (b1 `modu` b2) = bv_swrap n (bv_unsigned b1 `mod` bv_unsigned b2).
  Proof. unfold bv_signed. by rewrite bv_modu_unsigned. Qed.

  Lemma bv_divs_unsigned b1 b2 :
    bv_unsigned (b1 `divs` b2) = bv_wrap n (bv_signed b1 `div` bv_signed b2).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_divs_signed b1 b2 :
    bv_signed (b1 `divs` b2) = bv_swrap n (bv_signed b1 `div` bv_signed b2).
  Proof. apply Z_to_bv_signed. Qed.

  Lemma bv_quots_unsigned b1 b2 :
    bv_unsigned (b1 `quots` b2) = bv_wrap n (bv_signed b1 `quot` bv_signed b2).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_quots_signed b1 b2 :
    bv_signed (b1 `quots` b2) = bv_swrap n (bv_signed b1 `quot` bv_signed b2).
  Proof. apply Z_to_bv_signed. Qed.
  Lemma bv_quots_squot b1 b2 :
    bv_signed b2 ≠ 0 →
    bv_quots b1 b2 = Zmod.squot b1 b2.
  Proof.
    intros Hb2. apply bv_eq. rewrite bv_quots_unsigned.
    unfold Zmod.squot. rewrite !bv_signed_Zmod_signed in *.
    unfold bv_unsigned. rewrite Zmod.unsigned_of_Z.
    by rewrite (proj2 (Z.eqb_neq _ _)) by done.
  Qed.

  Lemma bv_mods_unsigned b1 b2 :
    bv_unsigned (b1 `mods` b2) = bv_wrap n (bv_signed b1 `mod` bv_signed b2).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_mods_signed b1 b2 :
    bv_signed (b1 `mods` b2) = bv_swrap n (bv_signed b1 `mod` bv_signed b2).
  Proof. apply Z_to_bv_signed. Qed.

  Lemma bv_rems_unsigned b1 b2 :
    bv_unsigned (b1 `rems` b2) = bv_wrap n (bv_signed b1 `rem` bv_signed b2).
  Proof. rewrite !bv_signed_Zmod_signed. apply Zmod.unsigned_of_Z. Qed.
  Lemma bv_rems_signed b1 b2 :
    bv_signed (b1 `rems` b2) = bv_swrap n (bv_signed b1 `rem` bv_signed b2).
  Proof. apply bv_signed_unsigned_wrap, bv_rems_unsigned. Qed.

  Lemma bv_shiftl_unsigned b1 b2 :
    bv_unsigned (b1 ≪ b2) = bv_wrap n (bv_unsigned b1 ≪ bv_unsigned b2).
  Proof. apply Zmod.unsigned_slu. Qed.
  Lemma bv_shiftl_signed b1 b2 :
    bv_signed (b1 ≪ b2) = bv_swrap n (bv_unsigned b1 ≪ bv_unsigned b2).
  Proof. apply bv_signed_unsigned_wrap, bv_shiftl_unsigned. Qed.

  Lemma bv_shiftr_unsigned b1 b2 :
    bv_unsigned (b1 ≫ b2) = bv_unsigned b1 ≫ bv_unsigned b2.
  Proof. apply Zmod.unsigned_sru. apply bv_unsigned_in_range. Qed.
  Lemma bv_shiftr_signed b1 b2 :
    bv_signed (b1 ≫ b2) = bv_swrap n (bv_unsigned b1 ≫ bv_unsigned b2).
  Proof. unfold bv_signed. by rewrite bv_shiftr_unsigned. Qed.

  Lemma bv_ashiftr_unsigned b1 b2 :
    bv_unsigned (b1 `ashiftr` b2) = bv_wrap n (bv_signed b1 ≫ bv_unsigned b2).
  Proof.
    rewrite bv_signed_Zmod_signed. apply Zmod.unsigned_srs. apply bv_unsigned_in_range.
  Qed.
  Lemma bv_ashiftr_signed b1 b2 :
    bv_signed (b1 `ashiftr` b2) = bv_swrap n (bv_signed b1 ≫ bv_unsigned b2).
  Proof. apply bv_signed_unsigned_wrap, bv_ashiftr_unsigned. Qed.

  Lemma bv_or_unsigned b1 b2 :
    bv_unsigned (bv_or b1 b2) = Z.lor (bv_unsigned b1) (bv_unsigned b2).
  Proof. apply bits.unsigned_or. Qed.
  Lemma bv_or_signed b1 b2 :
    bv_signed (bv_or b1 b2) = bv_swrap n (Z.lor (bv_unsigned b1) (bv_unsigned b2)).
  Proof. unfold bv_signed. by rewrite bv_or_unsigned. Qed.

  Lemma bv_and_unsigned b1 b2 :
    bv_unsigned (bv_and b1 b2) = Z.land (bv_unsigned b1) (bv_unsigned b2).
  Proof. apply bits.unsigned_and. Qed.
  Lemma bv_and_signed b1 b2 :
    bv_signed (bv_and b1 b2) = bv_swrap n (Z.land (bv_unsigned b1) (bv_unsigned b2)).
  Proof. unfold bv_signed. by rewrite bv_and_unsigned. Qed.

  Lemma bv_xor_unsigned b1 b2 :
    bv_unsigned (bv_xor b1 b2) = Z.lxor (bv_unsigned b1) (bv_unsigned b2).
  Proof. apply bits.unsigned_xor. Qed.
  Lemma bv_xor_signed b1 b2 :
    bv_signed (bv_xor b1 b2) = bv_swrap n (Z.lxor (bv_unsigned b1) (bv_unsigned b2)).
  Proof. unfold bv_signed. by rewrite bv_xor_unsigned. Qed.

  Lemma bv_not_unsigned b :
    bv_unsigned (bv_not b) = bv_wrap n (Z.lnot (bv_unsigned b)).
  Proof. apply Zmod.unsigned_of_Z. Qed.
  Lemma bv_not_signed b :
    bv_signed (bv_not b) = bv_swrap n (Z.lnot (bv_unsigned b)).
  Proof. apply bv_signed_unsigned_wrap, bv_not_unsigned. Qed.

  Lemma bv_zero_extend_unsigned' z b :
    bv_unsigned (bv_zero_extend z b) = bv_wrap z (bv_unsigned b).
  Proof. apply Zmod.unsigned_of_Z. Qed.
  (* [bv_zero_extend_unsigned] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_zero_extend_unsigned z b :
    (n ≤ z)%N →
    bv_unsigned (bv_zero_extend z b) = bv_unsigned b.
  Proof.
    intros ?. rewrite bv_zero_extend_unsigned', bv_wrap_small; [done|].
    bv_saturate. pose proof (bv_modulus_le_mono n z). lia.
  Qed.
  Lemma bv_zero_extend_signed z b :
    bv_signed (bv_zero_extend z b) = bv_swrap z (bv_unsigned b).
  Proof. apply bv_signed_unsigned_wrap, bv_zero_extend_unsigned'. Qed.

  Lemma bv_sign_extend_unsigned z b :
    bv_unsigned (bv_sign_extend z b) = bv_wrap z (bv_signed b).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_sign_extend_signed' z b :
    bv_signed (bv_sign_extend z b) = bv_swrap z (bv_signed b).
  Proof. apply Z_to_bv_signed. Qed.
  (* [bv_sign_extend_signed] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_sign_extend_signed z b :
    (n ≤ z)%N →
    bv_signed (bv_sign_extend z b) = bv_signed b.
  Proof.
    intros ?. rewrite bv_sign_extend_signed'.
    destruct (decide (n = 0%N)); subst.
    { by rewrite bv_signed_N_0, bv_swrap_0. }
    apply bv_swrap_small. bv_saturate.
    pose proof bv_half_modulus_le_mono n z. lia.
  Qed.

  Lemma bv_extract_unsigned s l b :
    bv_unsigned (bv_extract s l b) = bv_wrap l (bv_unsigned b ≫ Z.of_N s).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_extract_signed s l b :
    bv_signed (bv_extract s l b) = bv_swrap l (bv_unsigned b ≫ Z.of_N s).
  Proof. apply Z_to_bv_signed. Qed.
  Lemma bv_extract_slice s l b :
    bv_extract s l b = Zmod.firstn (Z.of_N l) (Zmod.skipn (Z.of_N s) b).
  Proof.
    apply bv_eq. rewrite bv_extract_unsigned. unfold bv_unsigned, bv_modulus.
    rewrite bits.unsigned_firstn, bits.unsigned_skipn by lia.
    by rewrite Z.shiftr_div_pow2 by lia.
  Qed.

  Lemma bv_concat_unsigned' m  n2 b1 (b2 : bv n2) :
    bv_unsigned (bv_concat m b1 b2) = bv_wrap m (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).
  Proof. apply Z_to_bv_unsigned. Qed.
  (* [bv_concat_unsigned] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_concat_unsigned m n2 b1 (b2 : bv n2) :
    (m = n + n2)%N →
    bv_unsigned (bv_concat m b1 b2) = Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2).
  Proof.
    intros ->. rewrite bv_concat_unsigned', bv_wrap_small; [done|].
    apply Z.bounded_iff_bits_nonneg'; [lia | |].
    { apply Z.lor_nonneg. bv_saturate. split; [|lia]. apply Z.shiftl_nonneg. lia. }
    intros k ?. rewrite Z.lor_spec, Z.shiftl_spec; [|lia].
    apply orb_false_intro; (eapply Z.bounded_iff_bits_nonneg; [..|done]); bv_saturate; try lia.
    - apply (Z.lt_le_trans _ (bv_modulus n)); [lia|]. apply Z.pow_le_mono_r; lia.
    - apply (Z.lt_le_trans _ (bv_modulus n2)); [lia|]. apply Z.pow_le_mono_r; lia.
  Qed.
  Lemma bv_concat_signed m n2 b1 (b2 : bv n2) :
    bv_signed (bv_concat m b1 b2) = bv_swrap m (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).
  Proof. apply Z_to_bv_signed. Qed.
  (* [Zmod.app] puts its first argument in the low bits, [bv_concat] in the high bits. *)
  Lemma bv_concat_app m n2 b1 (b2 : bv n2) :
    bv_concat m b1 b2 = Zmod.firstn (Z.of_N m) (Zmod.app b2 b1).
  Proof.
    apply bv_eq. rewrite bv_concat_unsigned'. unfold bv_unsigned, bv_modulus.
    rewrite bits.unsigned_firstn, bits.unsigned_app by lia.
    by rewrite Z.lor_comm.
  Qed.

  Lemma bv_add_Z_unsigned b z :
    bv_unsigned (b `+Z` z) = bv_wrap n (bv_unsigned b + z).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_add_Z_signed b z :
    bv_signed (b `+Z` z) = bv_swrap n (bv_signed b + z).
  Proof. unfold bv_add_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_sub_Z_unsigned b z :
    bv_unsigned (b `-Z` z) = bv_wrap n (bv_unsigned b - z).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_sub_Z_signed b z :
    bv_signed (b `-Z` z) = bv_swrap n (bv_signed b - z).
  Proof. unfold bv_sub_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_mul_Z_unsigned b z:
    bv_unsigned (b `*Z` z) = bv_wrap n (bv_unsigned b * z).
  Proof. apply Z_to_bv_unsigned. Qed.
  Lemma bv_mul_Z_signed b z :
    bv_signed (b `*Z` z) = bv_swrap n (bv_signed b * z).
  Proof. unfold bv_mul_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.
End unfolding.

(** ** Properties of bv operations *)
Section properties.
  Context {n : N}.
  Implicit Types (b : bv n).
  Local Open Scope bv_scope.

  Lemma bv_sub_add_opp b1 b2:
    b1 - b2 = b1 + - b2.
  Proof. symmetry. apply Zmod.add_opp_r. Qed.

  Global Instance bv_add_assoc : Assoc (=) (@bv_add n).
  Proof. intros ???. apply Zmod.add_assoc. Qed.

  Global Instance bv_mul_assoc : Assoc (=) (@bv_mul n).
  Proof. intros ???. apply Zmod.mul_assoc. Qed.

  Lemma bv_add_0_l b1 b2 :
    bv_unsigned b1 = 0%Z →
    b1 + b2 = b2.
  Proof.
    intros Hb. apply bv_eq.
    rewrite bv_add_unsigned, Hb, Z.add_0_l, bv_wrap_small; [done|apply bv_unsigned_in_range].
  Qed.

  Lemma bv_add_0_r b1 b2 :
    bv_unsigned b2 = 0%Z →
    b1 + b2 = b1.
  Proof.
    intros Hb. apply bv_eq.
    rewrite bv_add_unsigned, Hb, Z.add_0_r, bv_wrap_small; [done|apply bv_unsigned_in_range].
  Qed.

  Lemma bv_add_Z_0 b : b `+Z` 0 = b.
  Proof.
    unfold bv_add_Z. rewrite Z.add_0_r.
    apply bv_eq. apply Z_to_bv_small. apply bv_unsigned_in_range.
  Qed.

  Lemma bv_add_Z_add_r b m o:
    b `+Z` (m + o) = (b `+Z` o) `+Z` m.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
     bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_add_l b m o:
    b `+Z` (m + o) = (b `+Z` m) `+Z` o.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
     bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_succ b m:
    b `+Z` Z.succ m = (b `+Z` 1) `+Z` m.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_inj_l b i j:
    0 ≤ i < bv_modulus n →
    0 ≤ j < bv_modulus n →
    b `+Z` i = b `+Z` j ↔ i = j.
  Proof.
    intros ??. split; [|naive_solver].
    intros Heq%bv_eq. rewrite !bv_add_Z_unsigned, !(Z.add_comm (bv_unsigned _)) in Heq.
    by rewrite <-bv_wrap_add_inj, !bv_wrap_small in Heq.
  Qed.

  Lemma bv_opp_not b:
    - b `-Z` 1 = bv_not b.
  Proof.
    apply bv_eq.
    rewrite bv_not_unsigned, bv_sub_Z_unsigned, bv_opp_unsigned, <-Z.opp_lnot.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_and_comm b1 b2:
    bv_and b1 b2 = bv_and b2 b1.
  Proof. apply bv_eq. by rewrite !bv_and_unsigned, Z.land_comm. Qed.

  Lemma bv_or_comm b1 b2:
    bv_or b1 b2 = bv_or b2 b1.
  Proof. apply bv_eq. by rewrite !bv_or_unsigned, Z.lor_comm. Qed.

  Lemma bv_or_0_l b1 b2 :
    bv_unsigned b1 = 0%Z →
    bv_or b1 b2 = b2.
  Proof. intros Hb. apply bv_eq. by rewrite bv_or_unsigned, Hb, Z.lor_0_l. Qed.

  Lemma bv_or_0_r b1 b2 :
    bv_unsigned b2 = 0%Z →
    bv_or b1 b2 = b1.
  Proof. intros Hb. apply bv_eq. by rewrite bv_or_unsigned, Hb, Z.lor_0_r. Qed.

  Lemma bv_extract_0_unsigned l b:
    bv_unsigned (bv_extract 0 l b) = bv_wrap l (bv_unsigned b).
  Proof. rewrite bv_extract_unsigned, Z.shiftr_0_r. done. Qed.

  Lemma bv_extract_0_bv_add_distr l b1 b2:
    (l ≤ n)%N →
    bv_extract 0 l (bv_add b1 b2) = bv_add (bv_extract 0 l b1) (bv_extract 0 l b2).
  Proof.
    intros ?.
    apply bv_eq. rewrite !bv_extract_0_unsigned, !bv_add_unsigned, !bv_extract_0_unsigned.
    rewrite bv_wrap_bv_wrap by done.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_concat_0 m n2 b1 (b2 : bv n2) :
    bv_unsigned b1 = 0%Z →
    bv_concat m b1 b2 = bv_zero_extend m b2.
  Proof.
    intros Hb1. apply bv_eq.
    by rewrite bv_zero_extend_unsigned', bv_concat_unsigned', Hb1, Z.shiftl_0_l, Z.lor_0_l.
  Qed.

  Lemma bv_concat_extract_merge n1 n2 s k b :
    (n = n1 + n2)%N →
    (k = s + n1)%N →
    bv_concat n (bv_extract k n2 b) (bv_extract s n1 b) = bv_extract s n b.
  Proof.
    intros -> ->. apply bv_eq.
    rewrite bv_concat_unsigned, !bv_extract_unsigned, !bv_wrap_land; [|lia].
    apply Z.bits_inj_iff' => i ?.
    rewrite Z.lor_spec, Z.shiftl_spec, !Z.land_spec; [|done].
    rewrite (Z.shiftr_spec _ (Z.of_N s) _); [|done].
    (* Two cases i < n1 or i ≥ n1 *)
    rewrite (Z.ones_spec (Z.of_N n1) _); [|lia..].
    case_bool_decide.
    - rewrite (Z.testbit_neg_r _ (i - Z.of_N n1)); [|lia]; simpl.
      by rewrite !Z.ones_spec_low; [|lia..].
    - rewrite andb_false_r, orb_false_r, Z.shiftr_spec, Z.ones_spec; [|lia..].
      (* Bit test above bitvector, case of i ≥ n1+n2 *)
      case_bool_decide.
      + rewrite Z.ones_spec, bool_decide_eq_true_2; [|lia..].
        do 2 f_equal. lia.
      + by rewrite Z.ones_spec_high, !andb_false_r; [|lia].
  Qed.

  Lemma bv_concat_extract_id n1 n2 b :
    (n = n1 + n2)%N →
    bv_concat n (bv_extract n1 n2 b) (bv_extract 0 n1 b) = b.
  Proof.
    intros. rewrite bv_concat_extract_merge; [|lia..].
    apply bv_eq. by rewrite bv_extract_0_unsigned, bv_wrap_bv_unsigned.
  Qed.

  Lemma bv_zero_extend_idemp b:
    bv_zero_extend n b = b.
  Proof. apply bv_eq. by rewrite bv_zero_extend_unsigned. Qed.

  Lemma bv_sign_extend_idemp b:
    bv_sign_extend n b = b.
  Proof. apply bv_eq_signed. by rewrite bv_sign_extend_signed. Qed.
End properties.

(** ** Lemmas about [bv_to_little] and [bv_of_little] *)
Section little.

  Lemma bv_to_litte_endian_unsigned m n z:
    0 ≤ m →
    bv_unsigned <$> bv_to_little_endian m n z = Z_to_little_endian m (Z.of_N n) z.
  Proof.
    intros ?. apply list_eq. intros i. unfold bv_to_little_endian.
    rewrite list_lookup_fmap, list_lookup_fmap.
    destruct (Z_to_little_endian m (Z.of_N n) z !! i) eqn: Heq; [simpl |done].
    rewrite Z_to_bv_small; [done|].
    eapply (Forall_forall (λ z, _ ≤ z < _)); [ |by eapply list_elem_of_lookup_2].
    eapply Z_to_little_endian_bound; lia.
  Qed.

  Lemma bv_to_little_endian_to_bv m n bs:
    m = Z.of_nat (length bs) →
    bv_to_little_endian m n (little_endian_to_bv n bs) = bs.
  Proof.
    intros ->. apply (inj (fmap bv_unsigned)).
    rewrite bv_to_litte_endian_unsigned; [|lia].
    apply Z_to_little_endian_to_Z; [by rewrite length_fmap | lia |].
    apply Forall_forall. intros ? [?[->?]]%list_elem_of_fmap. apply bv_unsigned_in_range.
  Qed.

  Lemma little_endian_to_bv_to_little_endian m n z:
    0 ≤ m →
    little_endian_to_bv n (bv_to_little_endian m n z) = z `mod` 2 ^ (m * Z.of_N n).
  Proof.
    intros ?. unfold little_endian_to_bv.
    rewrite bv_to_litte_endian_unsigned; [|lia].
    apply little_endian_to_Z_to_little_endian; lia.
  Qed.

  Lemma length_bv_to_little_endian m n z :
    0 ≤ m →
    length (bv_to_little_endian m n z) = Z.to_nat m.
  Proof.
    intros ?. unfold bv_to_little_endian. rewrite length_fmap.
    apply Nat2Z.inj. rewrite length_Z_to_little_endian, ?Z2Nat.id; try lia.
  Qed.

  Lemma little_endian_to_bv_bound n bs :
    0 ≤ little_endian_to_bv n bs < 2 ^ (Z.of_nat (length bs) * Z.of_N n).
  Proof.
    unfold little_endian_to_bv. rewrite <-(length_fmap bv_unsigned bs).
    apply little_endian_to_Z_bound; [lia|].
    apply Forall_forall. intros ? [? [-> ?]]%list_elem_of_fmap.
    apply bv_unsigned_in_range.
  Qed.

  Lemma Z_to_bv_little_endian_to_bv_to_little_endian x m n (b : bv x):
    0 ≤ m →
    x = (Z.to_N m * n)%N →
    Z_to_bv x (little_endian_to_bv n (bv_to_little_endian m n (bv_unsigned b))) = b.
  Proof.
    intros ? ->. rewrite little_endian_to_bv_to_little_endian, Z.mod_small; [| |lia].
    - apply bv_eq. rewrite Z_to_bv_small; [done|]. apply bv_unsigned_in_range.
    - pose proof bv_unsigned_in_range _ b as Hr. unfold bv_modulus in Hr.
      by rewrite N2Z.inj_mul, Z2N.id in Hr.
  Qed.

  Lemma bv_to_little_endian_lookup_Some m n z (i : nat) x:
    0 ≤ m → bv_to_little_endian m n z !! i = Some x ↔
      Z.of_nat i < m ∧ x = Z_to_bv n (z ≫ (Z.of_nat i * Z.of_N n)).
  Proof.
    unfold bv_to_little_endian. intros Hm. rewrite list_lookup_fmap, fmap_Some.
    split.
    - intros [?[[??]%Z_to_little_endian_lookup_Some ?]]; [|lia..]; subst. split; [done|].
      rewrite <-bv_wrap_land. apply bv_eq. by rewrite !Z_to_bv_unsigned, bv_wrap_bv_wrap.
    - intros [?->]. eexists _. split; [apply Z_to_little_endian_lookup_Some; try done; lia| ].
      rewrite <-bv_wrap_land. apply bv_eq. by rewrite !Z_to_bv_unsigned, bv_wrap_bv_wrap.
  Qed.

  Lemma little_endian_to_bv_spec n bs i b:
    0 ≤ i → n ≠ 0%N →
    bs !! Z.to_nat (i `div` Z.of_N n) = Some b →
    Z.testbit (little_endian_to_bv n bs) i = Z.testbit (bv_unsigned b) (i `mod` Z.of_N n).
  Proof.
    intros ???. unfold little_endian_to_bv. apply little_endian_to_Z_spec; [lia|lia| |].
    { apply Forall_fmap. apply Forall_true. intros ?; simpl. apply bv_unsigned_in_range. }
    rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
  Qed.
End little.

(** ** Lemmas about [bv_seq] *)
Section bv_seq.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma length_bv_seq b len:
    length (bv_seq b len) = Z.to_nat len.
  Proof. unfold bv_seq. by rewrite length_fmap, length_seqZ. Qed.

  Lemma bv_seq_succ b m:
    0 ≤ m →
    bv_seq b (Z.succ m) = b :: bv_seq (b `+Z` 1) m.
  Proof.
    intros. unfold bv_seq. rewrite seqZ_cons by lia. csimpl.
    rewrite bv_add_Z_0. f_equal.
    assert (Z.succ 0 = 1 + 0) as -> by lia.
    rewrite <-fmap_add_seqZ, <-list_fmap_compose, Z.pred_succ. apply list_fmap_ext.
    intros i x. simpl. by rewrite bv_add_Z_add_l.
  Qed.

  Lemma NoDup_bv_seq b z:
    0 ≤ z ≤ bv_modulus n →
    NoDup (bv_seq b z).
  Proof.
    intros ?. apply NoDup_alt. intros i j b'. unfold bv_seq. rewrite !list_lookup_fmap.
    intros [?[[??]%lookup_seqZ ?]]%fmap_Some ; simplify_eq.
    intros [?[[->?]%lookup_seqZ ?%bv_add_Z_inj_l]]%fmap_Some; lia.
  Qed.
End bv_seq.

(** ** Lemmas about [bv] and [bool] *)
Section bv_bool.
  Implicit Types (b : bool).

  Lemma bool_to_bv_unsigned n b:
    n ≠ 0%N →
    bv_unsigned (bool_to_bv n b) = bool_to_Z b.
  Proof.
    intros ?. pose proof (bv_modulus_gt_1 n).
    apply Z_to_bv_small. destruct b; simpl; lia.
  Qed.

  Lemma bv_extract_bool_to_bv n n2 b:
    n ≠ 0%N → n2 ≠ 0%N →
    bv_extract 0 n (bool_to_bv n2 b) = bool_to_bv n b.
  Proof.
    intros ??. apply bv_eq. pose proof (bv_modulus_gt_1 n).
    rewrite bv_extract_unsigned, !bool_to_bv_unsigned, Z.shiftr_0_r by done.
    rewrite bv_wrap_small; [done|]. destruct b; simpl; lia.
  Qed.

  Lemma bv_not_bool_to_bv b:
    bv_not (bool_to_bv 1 b) = bool_to_bv 1 (negb b).
  Proof. apply bv_eq. by destruct b. Qed.

  Lemma bool_decide_bool_to_bv_0 b:
    bool_decide (bv_unsigned (bool_to_bv 1 b) = 0) = negb b.
  Proof. by destruct b. Qed.
  Lemma bool_decide_bool_to_bv_1 b:
    bool_decide (bv_unsigned (bool_to_bv 1 b) = 1) = b.
  Proof. by destruct b. Qed.
End bv_bool.

Section bv_bits.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma length_bv_to_bits b : length (bv_to_bits b) = N.to_nat n.
  Proof. unfold bv_to_bits. rewrite length_fmap, length_seqZ, <-Z_N_nat, N2Z.id. done. Qed.

  Lemma bv_to_bits_lookup_Some b i x:
    bv_to_bits b !! i = Some x ↔ (i < N.to_nat n)%nat ∧ x = Z.testbit (bv_unsigned b) (Z.of_nat i).
  Proof.
    unfold bv_to_bits. rewrite list_lookup_fmap, fmap_Some.
    split.
    - intros [?[?%lookup_seqZ?]]. naive_solver lia.
    - intros [??]. eexists _. split; [|done]. apply lookup_seqZ. lia.
  Qed.

  Global Instance bv_to_bits_inj : Inj eq eq (@bv_to_bits n).
  Proof.
    unfold bv_to_bits. intros x y Hf.
    apply bv_eq_wrap. apply Z.bits_inj_iff'. intros i Hi.
    rewrite !bv_wrap_spec; [|lia..]. case_bool_decide; simpl; [|done].
    eapply list_fmap_inj_1 in Hf; [done|]. apply elem_of_seqZ. lia.
  Qed.
End bv_bits.


(** * [bvn] *)
Record bvn := bv_to_bvn {
  bvn_n : N;
  bvn_val : bv bvn_n;
}.
Global Arguments bv_to_bvn {_} _.
Add Printing Constructor bvn.

Global Instance bv_to_bvn_inj {n} : Inj (=) (=) (@bv_to_bvn n).
Proof. intros Hb. naive_solver. Qed.

Definition bvn_unsigned (b : bvn) := bv_unsigned (b.(bvn_val)).

Lemma bvn_eq (b1 b2 : bvn) :
  b1 = b2 ↔ b1.(bvn_n) = b2.(bvn_n) ∧ bvn_unsigned b1 = bvn_unsigned b2.
Proof. split; [ naive_solver|]. destruct b1, b2; simpl; intros [??]. subst. f_equal. by apply bv_eq. Qed.

Global Program Instance bvn_eq_dec : EqDecision bvn := λ '(@bv_to_bvn n1 b1) '(@bv_to_bvn n2 b2),
   cast_if_and (decide (n1 = n2)) (decide (bv_unsigned b1 = bv_unsigned b2)).
(* TODO: The following does not compute to eq_refl*)
Next Obligation. intros. apply bvn_eq. naive_solver. Qed.
Next Obligation. intros. intros ?%bvn_eq. naive_solver. Qed.
Next Obligation. intros. intros ?%bvn_eq. naive_solver. Qed.

Definition bvn_to_bv (n : N) (b : bvn) : option (bv n) :=
  match decide (b.(bvn_n) = n) with
  | left eq => Some (eq_rect (bvn_n b) (λ n0 : N, bv n0) (bvn_val b) n eq)
  | right _ => None
  end.
Global Arguments bvn_to_bv !_ !_ /.

Global Coercion bv_to_bvn : bv >-> bvn.

(** * Opaqueness *)
(** We mark all functions on bitvectors as opaque. *)
(** The abbreviations ([bv_add], ...) are not in these lists: making them
opaque would make the [Zmod] operations opaque for every user of the
standard library. *)
Global Hint Opaque Z_to_bv
       bv_0 bv_succ bv_pred
       bv_divu
       bv_divs bv_quots bv_mods
       bv_shiftl bv_shiftr bv_ashiftr
       bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z
       bool_to_bv bv_to_bits : typeclass_instances.
Global Opaque Z_to_bv
       bv_0 bv_succ bv_pred
       bv_divu
       bv_divs bv_quots bv_mods
       bv_shiftl bv_shiftr bv_ashiftr
       bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z
       bool_to_bv bv_to_bits.
