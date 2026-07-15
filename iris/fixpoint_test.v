From iris.heap_lang Require Import proofmode notation.
From iris.bi.lib Require Import fixpoint_mono.

(* Representative example of a recursive predicate defined via least fixpoint:
   is_list v l = if v = NONE (null) then ⌜l = []⌝
                 else ∃ p x l' w, ⌜l = x :: l'⌝ ∗ ⌜v = SOME #p⌝ ∗ p ↦ (x, w) ∗ is_list w l' *)

Section list.
  Context `{!heapGS Σ}.

  Definition is_list_pre (rec : prodO valO (leibnizO (list Z)) → iProp Σ)
      : prodO valO (leibnizO (list Z)) → iProp Σ := λ vl,
    (if bool_decide (vl.1 = NONEV) then ⌜vl.2 = []⌝
     else ∃ (p : loc) (x : Z) (l' : list Z) (w : val),
       ⌜vl.2 = x :: l'⌝ ∗ ⌜vl.1 = SOMEV #p⌝ ∗ p ↦ (#x, w)%V ∗ rec (w, l'))%I.

  Local Instance is_list_pre_mono : BiMonoPred is_list_pre.
  Proof.
    split.
    - iIntros (Φ Ψ HΦ HΨ) "#Hmon %vl HF".
      rewrite /is_list_pre. case_bool_decide; first done.
      iDestruct "HF" as (p x l' w) "(% & % & Hp & Hrec)".
      iExists p, x, l', w. iFrame "Hp". do 2 (iSplit; first done).
      by iApply "Hmon".
    - intros Φ HΦ. solve_proper.
  Qed.

  Definition is_list (v : val) (l : list Z) : iProp Σ :=
    bi_least_fixpoint is_list_pre (v, l).

  Lemma is_list_unfold v l :
    is_list v l ⊣⊢ is_list_pre (λ vl, is_list vl.1 vl.2) (v, l).
  Proof.
    rewrite /is_list least_fixpoint_unfold //.
  Qed.
End list.
