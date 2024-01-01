From Coq Require Import Permutation.
From stdpp Require Import prelude vector.

Section voting.

  (* every element of A ("alternative") is a candidate *)
  Context {A: Type}.

  Record Vote :=
    { vote_lt : A → A → bool;
      (* TODO: might not need this, or might want vote_le instead *)
      vote_refl : ∀ x,
        negb (vote_lt x x);
      vote_trans : ∀ x y z,
        vote_lt x y → vote_lt y z → vote_lt x z;
      vote_antisym : ∀ x y,
        vote_lt x y = negb (vote_lt y x); }.
  Coercion vote_lt : Vote >-> Funclass.

  Context (Nvoters: nat).

  Definition ballot := vec Vote Nvoters.

  Implicit Types (v: Vote) (b: ballot).
  (* c is a candidates, i, j, n are voters *)
  Implicit Types (c: A) (i j n: fin Nvoters).

  (* constitution must be a total function from all ballots to a "vote" (a
  ranking of all candidates) *)
  Definition constitution := ballot → Vote.
  Record constitution_wf (C: constitution) :=
    { constitution_unanimity: ∀ b c1 c2,
        (∀ i, vote_lt (b !!! i) c1 c2) →
        C b c1 c2;
      constitution_iia: ∀ b1 b2 c1 c2,
        (* b1 and b2 have the same ordering of c1 and c2 (but irrelevant
        alternatives may have different rankings) *)
        (∀ i, vote_lt (b1 !!! i) c1 c2 =
                vote_lt (b2 !!! i) c1 c2) →
        C b1 c1 c2 = C b2 c1 c2;
    }.

  Definition arrows_thm := ∀ (C: constitution),
    constitution_wf C →
    (* we have three distinct candidates *)
    ∀ (A1 A2 A3: A) (Hne: A1 ≠ A2 ∧ A2 ≠ A3 ∧ A1 ≠ A3),
    ∃ n, ∀ b c1 c2, C b c1 c2 = vote_lt (b !!! n) c1 c2.

End voting.
