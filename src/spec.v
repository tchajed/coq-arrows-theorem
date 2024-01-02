From arrow Require Import options.

From stdpp Require Export prelude.

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

  Notation "c1 '⪯[' v ']' c2" := (vote_le v c1 c2)
                                   (at level 40, format "c1  ⪯[ v ]  c2").

  Context {Nvoters: nat}.

  Definition profile := vec Vote Nvoters.

  (* constitution must be a total function from all profiles to a "vote" (a
  ranking of all candidates) *)
  Definition constitution := profile → Vote.

  (* a, b, c are candidates, i, j, n are voters *)
  Implicit Types (a b c: A) (i j n: fin Nvoters).
  Implicit Types (v: Vote) (P: profile) (C: constitution).

  (* P1 and P2 are equivalent wrt the a b ordering *)
  Definition iia_at P1 P2 a b :=
    ∀ i, a ⪯[P1 !!! i] b = a ⪯[P2 !!! i] b.

  Class constitution_wf C :=
    { constitution_unanimity: ∀ P a b,
        (∀ i, a ⪯[P !!! i] b) →
        C P a b;
      constitution_iia: ∀ P1 P2 a b,
        (* P1 and P2 have the same ordering of c1 and c2 (but irrelevant
        alternatives may have different rankings) *)
        iia_at P1 P2 a b →
        C P1 a b = C P2 a b;
    }.

  Definition arrows_thm := ∀ C, constitution_wf C →
    (* we have three distinct candidates *)
    ∀ (A1 A2 A3: A) (Hne: A1 ≠ A2 ∧ A2 ≠ A3 ∧ A1 ≠ A3),
    ∃ n, ∀ P a b, C P a b = a ⪯[P !!! n] b.

End voting.

Notation "c1 '⪯[' v ']' c2" := (vote_le v c1 c2)
                                  (at level 40, format "c1  ⪯[ v ]  c2").

Arguments Vote A : clear implicits.
Arguments profile A Nvoters : clear implicits.
Arguments constitution A Nvoters : clear implicits.
