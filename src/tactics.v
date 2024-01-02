From arrow Require Import options.
From stdpp Require Import prelude.

Ltac simplify_decide :=
  repeat
    match goal with
    | |- context[decide ?P] =>
        first [ rewrite -> (decide_True (P:=P)) by auto
              | rewrite -> (decide_False (P:=P)) by auto
          ]
    end.
