From arrow Require Import options.

From stdpp Require Import vector ssreflect.

From arrow Require Import spec tactics.
From arrow Require classical.

Section voting.

  (* every element of A ("alternative") is a candidate *)
  Context {A: Type}.
  Context {Heq: EqDecision A}.

  Context (Nvoters: nat).

  Notation Vote := (Vote A).
  Notation profile := (profile A Nvoters).
  Notation constitution := (constitution A Nvoters).

  (* a, b, c are candidates, i, j, n are voters *)
  Implicit Types (a b c: A) (i j n: fin Nvoters).
  Implicit Types (v: Vote) (P: profile) (C: constitution).

  Lemma vote_antisym' (v: Vote) x y :
    x ⪯[v] y → y ⪯[v] x → x = y.
  Proof using Heq.
    intros.
    destruct (decide (x = y)); auto.
    pose proof (vote_antisym v x y ltac:(auto)).
    intuition.
  Qed.

  Lemma not_vote_le (v: Vote) (a b: A) :
    ¬(a ⪯[v] b) ↔ (b ⪯[v] a ∧ a ≠ b).
  Proof.
    pose proof (vote_refl v a) as Hrefl.
    pose proof (vote_antisym v b a) as Hanti1.
    pose proof (vote_antisym v a b) as Hanti2.
    split.
    - intros H.
      destruct (classical.excluded_middle (a = b)); subst; intuition.
    - intuition.
  Qed.

  Lemma decide_vote (v: Vote) (a b: A) :
    {vote_le v a b = true ∧ a ⪯[v] b} +
      {vote_le v a b = false ∧ b ⪯[v] a ∧ a ≠ b}.
  Proof.
    destruct (a ⪯[v] b) eqn:Hab; [ left | right ]; auto.
    assert (¬ a ⪯[v] b) as H%not_vote_le; [ | by intuition eauto ].
    rewrite Hab; auto.
  Qed.

  Ltac decide_vote v a c :=
    let Hac1 := fresh "H" a c "1" in
    let Hac2 := fresh "H" a c "2" in
    let Hne := fresh "Hne" in
    destruct (decide_vote v a c) as [[Hac1 Hac2] | (Hac1 & Hac2 & Hne)];
    try rewrite -> Hac1 in *.

  Lemma vote_refl_eq (v: Vote) a :
    vote_le v a a = true.
  Proof.
    decide_vote v a a; auto.
  Qed.

  (* b is polarizing for vote v if it is at the top or bottom *)
  Definition polarizing_vote (v: Vote) (b: A) :=
    (∀ c', b ⪯[v] c') ∨ (∀ c', c' ⪯[v] b).

  Lemma not_polarizing_surround (v: Vote) (b: A) :
    ~polarizing_vote v b →
    ∃ a c, a ≠ b ∧ b ≠ c ∧ a ⪯[v] b ∧ b ⪯[v] c.
  Proof.
    rewrite /polarizing_vote.
    rewrite classical.not_or !classical.not_all.
    setoid_rewrite not_vote_le.
    intros [(a & Hab & Hne1) (c & Hbc & Hne2)].
    exists a, c; intuition.
  Qed.

  (** We need to develop a way to re-arrange a vote. The low-level tool for this
  is a function which moves c to be above a in the ordering, changing as little
  else as possible. *)

  Definition move_vote_le (v: Vote) c a (x y: A) : bool :=
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

  Lemma move_refl v (c a x : A) :
    move_vote_le v c a x x.
  Proof.
    rewrite /move_vote_le.
    pose proof (vote_refl v x).
    decide_vote v a c; auto.
    destruct (decide (x = c)); subst; eauto.
  Qed.

  Lemma move_trans v (c a x y z : A) :
    move_vote_le v c a x y →
    move_vote_le v c a y z →
    move_vote_le v c a x z.
  Proof.
    rewrite /move_vote_le.
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

  Lemma move_antisym v (c a x y : A) :
    x ≠ y →
    move_vote_le v c a x y ↔ ¬ move_vote_le v c a y x.
  Proof.
    rewrite /move_vote_le.
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

  (** changes a vote to move c before a but leave other relative rankings the
  same *)
  Definition move_vote (v: Vote) c a : Vote.
    refine {| vote_le := move_vote_le v c a |}.
    - apply move_refl.
    - apply move_trans.
    - apply move_antisym.
  Defined.

  Class move_vote_characterize (v: Vote) c a :=
    { move_vote_at : a ⪯[move_vote v c a] c;
      move_vote_others : ∀ x y, x ≠ c ∧ y ≠ c →
            x ⪯[move_vote v c a] y = x ⪯[v] y;
      move_vote_below_c : ∀ x, x ⪯[v] c → x ⪯[move_vote v c a] c;
      move_vote_above_a : ∀ y, a ⪯[v] y → a ⪯[move_vote v c a] y;
    }.

  Instance move_vote_characterize_ok (v: Vote) c a :
    move_vote_characterize v c a.
  Proof.
    decide_vote v a c; auto.
    { constructor; rewrite /move_vote /= /move_vote_le;
        rewrite Hac1 //. }
    constructor; rewrite /move_vote /= /move_vote_le;
      rewrite Hac1 //; intros;
      destruct_and?;
        simplify_decide; auto.
    - auto using vote_refl.
    - repeat destruct (decide _); subst; eauto using vote_trans.
    - repeat destruct (decide _); subst; eauto using vote_trans.
  Qed.

  Definition move_c_before_a P c a : profile :=
    vmap (λ v, move_vote v c a) P.

  Lemma move_c_before_a_lookup P c a i :
    move_c_before_a P c a !!! i = move_vote (P !!! i) c a.
  Proof.
    rewrite /move_c_before_a vlookup_map //.
  Qed.

  Lemma order_both_false (v1 v2: Vote) a b :
    b ⪯[v1] a →
    b ⪯[v2] a →
    a ⪯[v1] b = a ⪯[v2] b.
  Proof.
    intros.
    destruct (classical.excluded_middle (a = b));
      subst; [ rewrite !vote_refl_eq // | ].
    pose proof (vote_antisym v1 b a).
    pose proof (vote_antisym v2 b a).
    decide_vote v1 a b; intuition auto.
    decide_vote v2 a b; intuition auto.
  Qed.

  Lemma order_both_true (v1 v2: Vote) a b :
    a ⪯[v1] b →
    a ⪯[v2] b →
    a ⪯[v1] b = a ⪯[v2] b.
  Proof.
    rewrite /Is_true.
    intros.
    destruct (a ⪯[v1] b); intuition.
    destruct (a ⪯[v2] b); intuition.
  Qed.

  Lemma polarizing_prefs_polarizing C (Hwf: constitution_wf C) :
    ∀ P (b: A),
    (∀ i, polarizing_vote (P !!! i) b) →
    polarizing_vote (C P) b.
  Proof using Heq.
    intros * Hpolar_voters.
    apply classical.not_not;
      intros (c & a & Hne1 & Hne2 & Hcb & Hba)%not_polarizing_surround.
    assert (a ≠ c).
    { intros ->. contradict Hba.
      eapply vote_antisym; eauto. }
    assert (c ⪯[C P] a) as Hca by eauto using vote_trans.

    (* need to construct a new profile P' from P that moves c above a in every
    profile *)

    pose (P' := move_c_before_a P c a).
    assert (a ⪯[C P'] c) as HP'ca.
    { apply constitution_unanimity; intros.
      subst P'.
      rewrite move_c_before_a_lookup.
      apply move_vote_at. }
    assert (iia_at P P' b a) as Hiia_ab.
    { intros i. subst P'. rewrite move_c_before_a_lookup.
      set (v := P !!! i).
      destruct (Hpolar_voters i) as [Hi | Hi].
      - apply order_both_true; [ by eauto | ].
        rewrite move_vote_others //.
      - apply order_both_false; [ by eauto | ].
        rewrite move_vote_others //. }
    assert (iia_at P P' c b) as Hiia_bc.
    { intros i. subst P'. rewrite move_c_before_a_lookup.
      set (v := P !!! i).
      destruct (Hpolar_voters i) as [Hi | Hi].
      - apply order_both_false; [ by eauto | ].
        apply move_vote_below_c; auto.
      - apply order_both_true; [ by eauto | ].
        rewrite /move_vote /= /move_vote_le.
        decide_vote v a c; auto.
        simplify_decide; auto. }

    apply constitution_iia in Hiia_ab.
    apply constitution_iia in Hiia_bc.
    apply eq_bool_prop_elim in Hiia_ab, Hiia_bc.
    intuition.
    assert (c ⪯[C P'] a) by eauto using vote_trans.
    eauto using vote_antisym'.
  Qed.

End voting.
