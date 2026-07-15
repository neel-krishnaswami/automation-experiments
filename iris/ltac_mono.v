From iris.heap_lang Require Import proofmode notation.
From iris.bi.lib Require Import fixpoint_mono.

(** [solve_mono_go] proves goals of the form [body[Φ] -∗ body[Ψ]] (after
    [iIntros "HF"], so: goal [body[Ψ]] with "HF" : [body[Φ]]) for bodies
    generated from the grammar

      P ::= ∃ x:A. P | l ↦ v | ⊤ | ⊥ | P ∗ Q | ⌜ϕ⌝ ∧ P | ⌜ϕ⌝ | if b then P else Q | f(e)

    assuming the intuitionistic context contains
      "Hmon" : □ (∀ y, Φ y -∗ Ψ y).

    Invariant: goal and "HF" have identical shape, differing only at
    recursive-call leaves (Ψ vs Φ). At each node:
    - Φ-free subterm (↦, ⊤, ⊥, ⌜ϕ⌝, or anything not mentioning f): [iExact]
    - recursive call f(e): apply "Hmon"
    - ∃ / ∗ / ∧ / if: mirror the structure and recurse. *)
Ltac solve_mono_go :=
  cbv beta iota zeta;
  first
    [ iExact "HF"
    | iApply "Hmon"; iExact "HF"
    | lazymatch goal with
      | |- environments.envs_entails _ (bi_exist _) =>
          let x := fresh "x" in
          iDestruct "HF" as (x) "HF"; iExists x; solve_mono_go
      | |- environments.envs_entails _ (bi_sep _ _) =>
          iDestruct "HF" as "[HF1 HF2]";
          iSplitL "HF1";
          [ iRename "HF1" into "HF" | iRename "HF2" into "HF" ];
          solve_mono_go
      | |- environments.envs_entails _ (bi_and _ _) =>
          iSplit;
          [ iDestruct "HF" as "[HF _]" | iDestruct "HF" as "[_ HF]" ];
          solve_mono_go
      | |- environments.envs_entails _ (if ?b then _ else _) =>
          destruct b; solve_mono_go
      | |- environments.envs_entails _ (match ?p with pair _ _ => _ end) =>
          destruct p; solve_mono_go
      | |- _ => fail "solve_mono_go: unsupported connective in body"
      end ].

(** Full [BiMonoPred] solver: [solve_bi_mono_pred F_pre] where [F_pre] is the
    pre-fixpoint functional. Handles both the internal-monotonicity and the
    non-expansiveness obligations. *)
Ltac solve_bi_mono_pred F :=
  split;
  [ iIntros (Φ Ψ HΦ HΨ) "#Hmon %y HF"; unfold F; solve_mono_go
  | intros ? ?; solve_proper ].

(** * Tests *)
Section tests.
  Context `{!heapGS Σ}.

  (** Test 1: the linked-list predicate (if / ∃ / ⌜ϕ⌝ / ∗ / ↦ / f(e)). *)
  Definition is_list_pre (rec : prodO valO (leibnizO (list Z)) → iProp Σ)
      : prodO valO (leibnizO (list Z)) → iProp Σ := λ vl,
    (if bool_decide (vl.1 = NONEV) then ⌜vl.2 = []⌝
     else ∃ (p : loc) (x : Z) (l' : list Z) (w : val),
       ⌜vl.2 = x :: l'⌝ ∗ ⌜vl.1 = SOMEV #p⌝ ∗ p ↦ (#x, w)%V ∗ rec (w, l'))%I.

  Local Instance is_list_pre_mono : BiMonoPred is_list_pre.
  Proof. solve_bi_mono_pred is_list_pre. Qed.

  (** Test 2: exercises the rest of the grammar: ⊤, ⊥, plain bool if,
      nested ifs, ∧ with a pure proposition, and multiple recursive calls. *)
  Definition gnarly_pre
      (rec : prodO (leibnizO bool) (prodO valO (leibnizO (list Z))) → iProp Σ)
      : prodO (leibnizO bool) (prodO valO (leibnizO (list Z))) → iProp Σ := λ a,
    (if a.1
     then ⌜a.2.2 = []⌝ ∗ True
     else if bool_decide (a.2.1 = NONEV)
          then False
          else ∃ (p : loc) (w : val) (x : Z) (l' : list Z),
            ⌜a.2.2 = x :: l'⌝ ∗ p ↦ w ∗
            (⌜x = 0%Z⌝ ∧ rec (true, (w, l'))) ∗
            rec (false, (w, l')))%I.

  Local Instance gnarly_pre_mono : BiMonoPred gnarly_pre.
  Proof. solve_bi_mono_pred gnarly_pre. Qed.

  (** Test 3: pattern-matching lambdas, including a nested pattern. *)
  Definition plist_pre
      (rec : prodO valO (prodO (leibnizO (list Z)) (leibnizO bool)) → iProp Σ)
      : prodO valO (prodO (leibnizO (list Z)) (leibnizO bool)) → iProp Σ :=
    λ '(v, (l, strict)),
    (if bool_decide (v = NONEV) then (if strict then ⌜l = []⌝ else True)
     else ∃ (p : loc) (x : Z) (l' : list Z) (w : val),
       ⌜l = x :: l'⌝ ∗ ⌜v = SOMEV #p⌝ ∗ p ↦ (#x, w)%V ∗ rec (w, (l', strict)))%I.

  Local Instance plist_pre_mono : BiMonoPred plist_pre.
  Proof. solve_bi_mono_pred plist_pre. Qed.

  (** The fixpoints and their unfolding lemmas now come for free. *)
  Definition is_list (v : val) (l : list Z) : iProp Σ :=
    bi_least_fixpoint is_list_pre (v, l).

  Lemma is_list_unfold v l :
    is_list v l ⊣⊢ is_list_pre (λ vl, is_list vl.1 vl.2) (v, l).
  Proof. rewrite /is_list least_fixpoint_unfold //. Qed.
End tests.
