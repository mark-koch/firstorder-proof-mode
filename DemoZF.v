Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import ProofMode.
Require Import ZF.
Require Import Equations.Equations Equations.Prop.DepElim.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope string_scope.

Section ZF.

Variable p : peirce.

Ltac custom_fold ::= fold sub in *.
Ltac custom_unfold ::= unfold sub in *.


Definition ax_refl := ∀ $0 ≡ $0.
Definition ax_sym := ∀ ∀ $1 ≡ $0 --> $0 ≡ $1.
Definition ax_trans := ∀ ∀ ∀ $2 ≡ $1 --> $1 ≡ $0 --> $2 ≡ $0.
Definition ax_eq_elem := ∀ ∀ ∀ ∀ $3 ≡ $1 --> $2 ≡ $0 --> $3 ∈ $2 --> $1 ∈ $0.

Definition ZF := ax_ext::ax_eset::ax_pair::ax_union::ax_power::ax_om1::ax_om2::ax_refl::ax_sym::ax_trans::ax_eq_elem::nil.


Program Instance ZF_Leibniz : Leibniz ZF_func_sig ZF_pred_sig.
Next Obligation. exact equal. Defined.
Next Obligation. exact ZF. Defined.
Next Obligation. exact (fun phi => phi el ZF). Defined.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.


Lemma ZF_sub_pair' x y x' y' :
  ZF ⊢ (x ≡ x' --> y ≡ y'--> sub ({x; y}) ({x'; y'})).
Proof.
  fstart. fintros "H1" "H2" z. fapply ax_pair. fintros "H3".
  fapply ax_pair. frewrite <- "H1". frewrite <- "H2".
  fapply ax_pair. ctx.
Qed.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊢ (x ≡ x' --> y ≡ y'--> {x; y} ≡ {x'; y'}).
Proof.
  fstart. fintros "H1" "H2". fapply ax_ext.
  - fapply ZF_sub_pair'; ctx.
  - fapply ZF_sub_pair'; fapply ax_sym; ctx.
Qed.

Lemma ZF_union_el' x y z :
  ZF ⊢ (y ∈ x ∧ z ∈ y --> z ∈ ⋃ x).
Proof.
  fstart. fintros "[H1 H2]". fapply ax_union. fexists y. fsplit; ctx. 
Qed.

Lemma ZF_sub_union x y :
  ZF ⊢ (x ≡ y --> (⋃ x) ⊆ (⋃ y)).
Proof.
  fstart. fintros "H" z. frewrite "H". fintros; ctx.
Qed.

Lemma ZF_eq_union x y :
  ZF ⊢ (x ≡ y --> ⋃ x ≡ ⋃ y).
Proof.
  fstart. fintros "H". frewrite "H". fapply ax_refl.
Qed.

Lemma ZF_bunion_el' x y z :
  ZF ⊢ ((z ∈ x ∨ z ∈ y) --> z ∈ x ∪ y).
Proof.
  fstart. fintros "[H|H]".
  - fapply ax_union. fexists x. fsplit. fapply ax_pair. fleft. fapply ax_refl. ctx.
  - fapply ax_union. fexists y. fsplit. fapply ax_pair. fright. fapply ax_refl. ctx.
Qed.

Lemma ZF_bunion_inv' x y z :
  ZF ⊢ (z ∈ x ∪ y --> z ∈ x ∨ z ∈ y).
Proof.
  fstart. fintros "H". fapply ax_union in "H" as "[ [H1 H2]]". rename x0 into a.
  feapply ax_pair in "H1" as "[H1|H1]".
  - fleft. frewrite <- "H1". ctx.
  - fright. frewrite <- "H1". ctx.
Qed.
  

  