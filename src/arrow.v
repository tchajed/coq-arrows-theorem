From Coq Require Import ssreflect.
From Coq Require Import Permutation.
From Coq Require Logic.Classical.
From stdpp Require Import prelude vector.

Set Default Proof Using "Type".
Set Default Goal Selector "!".
Open Scope general_if_scope.

Module classical.
  Import Coq.Logic.Classical.

  Lemma not_not (P: Prop) :
    ~~P ↔ P.
  Proof. tauto. Qed.
  Lemma not_or (P Q: Prop) :
    ~(P ∨ Q) ↔ ~P ∧ ~Q.
  Proof. tauto. Qed.
  Lemma not_and (P Q: Prop) :
    ~(P ∧ Q) ↔ ~P ∨ ~Q.
  Proof. tauto. Qed.
  Lemma not_all (A: Type) (P: A → Prop) :
    (~∀ x, P x) ↔ ∃ x, ~P x.
  Proof.
    split.
    - apply not_all_ex_not.
    - apply ex_not_not_all.
  Qed.
  Lemma not_ex (A: Type) (P: A → Prop) :
    (~∃ x, P x) ↔ (∀ x, ~P x).
  Proof.
    rewrite -(not_not (∀ x, ~P x)).
    rewrite not_all.
    setoid_rewrite not_not.
    reflexivity.
  Qed.

  Lemma excluded_middle (P: Prop) : P ∨ ¬P.
  Proof. apply Classical_Prop.classic. Qed.

End classical.

Section voting.

  (* every element of A ("alternative") is a candidate *)
  Context {A: Type}.
  Context {Heq: EqDecision A}.

  Record Vote :=
    { vote_le : A → A → bool;
      vote_refl : ∀ x, vote_le x x;
      vote_trans : ∀ x y z,
        vote_le x y → vote_le y z → vote_le x z;
      vote_antisym : ∀ x y,
        x ≠ y →
        vote_le x y ↔ ¬(vote_le y x); }.
  Coercion vote_le : Vote >-> Funclass.

  Notation "c1 '⪯[' v ']' c2" := (vote_le v c1 c2) (at level 40,
                                     format "c1  ⪯[ v ]  c2").


  Context (Nvoters: nat).

  Definition profile := vec Vote Nvoters.

  Implicit Types (v: Vote) (P: profile).
  (* a, b, c are candidates, i, j, n are voters *)
  Implicit Types (a b c: A) (i j n: fin Nvoters).

  (* constitution must be a total function from all profiles to a "vote" (a
  ranking of all candidates) *)
  Definition constitution := profile → Vote.

  Implicit Types (C: constitution).

  Record constitution_wf C :=
    { constitution_unanimity: ∀ P a b,
        (∀ i, a ⪯[P !!! i] b) →
        C P a b;
      constitution_iia: ∀ P1 P2 a b,
        (* P1 and P2 have the same ordering of c1 and c2 (but irrelevant
        alternatives may have different rankings) *)
        (∀ i, a ⪯[P1 !!! i] b =
                a ⪯[P2 !!! i] b) →
        C P1 a b = C P2 a b;
    }.

  Definition arrows_thm := ∀ C, constitution_wf C →
    (* we have three distinct candidates *)
    ∀ (A1 A2 A3: A) (Hne: A1 ≠ A2 ∧ A2 ≠ A3 ∧ A1 ≠ A3),
    ∃ n, ∀ P a b, C P a b = a ⪯[P !!! n] b.

  (* b is polarizing for vote v if it is at the top or bottom *)
  Definition polarizing_vote (v: Vote) (b: A) :=
    (∀ c', b ⪯[v] c') ∨ (∀ c', c' ⪯[v] b).

  Lemma Is_true_elim (b: bool) :
    Is_true b ↔ b = true.
  Proof.
    destruct b; rewrite /Is_true /=; intuition (try congruence).
  Qed.
  Lemma Is_true_not_elim (b: bool) :
    ~Is_true b ↔ b = false.
  Proof.
    destruct b; rewrite /Is_true /=; intuition (try congruence).
  Qed.

  Lemma not_vote_le (v: Vote) (a b: A) :
    ¬(a ⪯[v] b) ↔ (b ⪯[v] a ∧ a ≠ b).
  Proof using Heq.
    pose proof (vote_refl v a) as Hrefl.
    pose proof (vote_antisym v b a) as Hanti1.
    pose proof (vote_antisym v a b) as Hanti2.
    split.
    - intros H.
      destruct (decide (a = b)); subst; intuition.
    - intuition.
  Qed.

  Lemma decide_vote (v: Vote) (a b: A) :
    {vote_le v a b = true ∧ a ⪯[v] b} +
      {vote_le v a b = false ∧ b ⪯[v] a ∧ a ≠ b}.
  Proof using Heq.
    destruct (a ⪯[v] b) eqn:Hab; [ left | right ]; auto.
    assert (¬ a ⪯[v] b) as H%not_vote_le; [ | by intuition eauto ].
    rewrite Hab; auto.
  Qed.

  Lemma not_polarizing_surround (v: Vote) (b: A) :
    ~polarizing_vote v b →
    ∃ a c, a ≠ b ∧ b ≠ c ∧ a ⪯[v] b ∧ b ⪯[v] c.
  Proof using Heq.
    rewrite /polarizing_vote.
    rewrite classical.not_or !classical.not_all.
    setoid_rewrite not_vote_le.
    intros [(a & Hab & Hne1) (c & Hbc & Hne2)].
    exists a, c; intuition.
  Qed.

  Lemma vote_refl_true (v: Vote) a :
    a ⪯[v] a ↔ True.
  Proof.
    split; intuition.
    apply vote_refl.
  Qed.

  Ltac decide_vote v a c :=
    let Hac1 := fresh "H" a c "1" in
    let Hac2 := fresh "H" a c "2" in
    let Hne := fresh "Hne" in
    destruct (decide_vote v a c) as [[Hac1 Hac2] | (Hac1 & Hac2 & Hne)];
    try rewrite -> Hac1 in *.

  Definition c_before_a_vote_le (v: Vote) c a (x y: A) : bool :=
    if a ⪯[v] c then x ⪯[v] y
    else
      (if decide (x = c) then
         (if decide (y = c) then true
          else if decide (y = a) then false
               else a ⪯[v] y)
       else
         if decide (y = c) then
           x ⪯[v] a
         else x ⪯[v] y).

  Lemma c_before_a_refl v (c a x : A) :
    c_before_a_vote_le v c a x x.
  Proof.
    rewrite /c_before_a_vote_le.
    pose proof (vote_refl v x).
    decide_vote v a c; auto.
    destruct (decide (x = c)); subst; eauto.
  Qed.

  Lemma c_before_a_trans v (c a x y z : A) :
      c_before_a_vote_le v c a x y →
      c_before_a_vote_le v c a y z →
      c_before_a_vote_le v c a x z.
    Proof.
      rewrite /c_before_a_vote_le.
      pose proof (vote_trans v x y z) as Hvtrans.
      intros H.
      destruct (a ⪯[v] c) eqn:?; [ by auto | ].
      assert (¬a ⪯[v] c) as Hca.
      { intros H'.
        rewrite Heqb in H'; auto. }
      apply not_vote_le in Hca as [Hca Hne].
      repeat
        destruct (decide _)
        || lazymatch goal with
          | H: context[decide ?P] |- _ => destruct (decide P)
          end
        || subst
        || eauto using vote_trans.
      intros.
      contradict H.
      apply not_vote_le; eauto.
    Qed.

    Lemma c_before_a_antisym v (c a x y : A) :
      x ≠ y →
      c_before_a_vote_le v c a x y ↔ ¬ c_before_a_vote_le v c a y x.
    Proof.
      rewrite /c_before_a_vote_le.
      intros Hne.
      pose proof (vote_antisym v x y ltac:(auto)).
      pose proof (vote_antisym v y x ltac:(auto)).
      decide_vote v a c; eauto using vote_antisym.
      destruct (decide (x = c));
        destruct (decide (y = c));
        subst;
        try solve [ intuition eauto ].
      * destruct (decide (y = a)); subst; eauto using vote_antisym.
        pose proof (vote_refl v a). intuition eauto.
      * destruct (decide (x = a)); subst; eauto using vote_antisym.
        pose proof (vote_refl v a). intuition eauto.
    Qed.

  Definition move_c_before_a_vote (v: Vote) c a : Vote.
    refine {| vote_le := c_before_a_vote_le v c a |}.
    - (* refl *)
      apply c_before_a_refl.
    - (* trans *)
      apply c_before_a_trans.
    - (* antisym *)
      apply c_before_a_antisym.
  Defined.

  Lemma move_c_before_a_characterize (v: Vote) c a :
    a ⪯[move_c_before_a_vote v c a] c.
  Proof.
    rewrite /move_c_before_a_vote /= /c_before_a_vote_le.
    decide_vote v a c; auto.
    destruct (decide (a = c)); [ congruence | ].
    destruct (decide (c = c)); [ | congruence ].
    auto using vote_refl.
  Qed.

  Definition move_c_before_a P c a : profile :=
    vmap (λ v, move_c_before_a_vote v c a) P.

  Lemma polarizing_prefs_polarizing C (Hwf: constitution_wf C) :
    ∀ P (b: A),
    (∀ i, polarizing_vote (P !!! i) b) →
    polarizing_vote (C P) b.
  Proof.
    intros * Hpolar_voters.
    apply classical.not_not;
      intros (a & c & Hne1 & Hne2 & Hab & Hbc)%not_polarizing_surround.

    (* need to construct a new profile P' from P that moves c above a in every
    profile *)

  Abort.

End voting.
