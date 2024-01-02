From arrow Require Import options.
From stdpp Require Import prelude.
From Coq Require Import Logic.Classical.

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
  rewrite <- (not_not (∀ x, ~P x)).
  rewrite not_all.
  setoid_rewrite not_not.
  reflexivity.
Qed.

Lemma excluded_middle (P: Prop) : P ∨ ¬P.
Proof. apply Classical_Prop.classic. Qed.
