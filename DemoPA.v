Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import ProofMode.
Require Import Theories.
Require Import PA.
Require Import Equations.Equations Equations.Prop.DepElim.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope string_scope.


Section FullLogic.
Variable p : peirce.


(** Setup *)

Instance eqdec_funcs : EqDec PA_funcs_signature.
Proof. intros x y; decide equality. Qed.

Instance eqdec_preds : EqDec PA_preds_signature.
Proof. intros x y. destruct x, y. now left. Qed.

Ltac custom_fold ::= fold zero in *.
Ltac custom_unfold ::= unfold zero in *.
Ltac custom_simpl ::= try rewrite !numeral_subst_invariance.



(** Proof mode and tactics demo *)

Goal forall a b c, nil ⊢ (a --> (a --> b) --> (b --> c) --> c).
Proof.
  intros. fstart. fintros. fapply "H1". fapply "H0". fapply "H".
Qed.

Lemma num_add_homomorphism x y :
  FA ⊢ (num x ⊕ num y == num (x + y)).
Proof.
  induction x; cbn.
  - fapply ax_add_zero. (* Arguments are infered! *)
  - feapply ax_trans.
    + fapply ax_add_rec. 
    + feapply ax_eq_succ. exact IHx.
Qed.

Lemma num_mult_homomorphism x y : FA ⊢ ( num x ⊗ num y == num (x * y) ).
Proof.
  induction x; cbn.
  - fapply ax_mult_zero.
  - feapply ax_trans.
    + feapply ax_trans.
      * fapply ax_mult_rec.
      * feapply ax_eq_add. fapply ax_refl. exact IHx.
    + apply num_add_homomorphism.
Qed.




(** Setup rewriting *)

Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature.
Next Obligation. exact Eq. Defined.
Next Obligation. exact FA. Defined.
Next Obligation. exact (fun phi => phi el FA). Defined.
Next Obligation. apply Ctx. firstorder. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.




(* Rewriting allows for more elegant proofs *)

Lemma num_add_homomorphism' x y :
  FA ⊢ (num x ⊕ num y == num (x + y)).
Proof.
  induction x; cbn.
  - fapply ax_add_zero.
  - frewrite <- IHx. fapply ax_add_rec.
Qed.

Lemma num_mult_homomorphism' x y : FA ⊢ ( num x ⊗ num y == num (x * y) ).
Proof.
  induction x; cbn.
  - fapply ax_mult_zero.
  - frewrite (ax_mult_rec (num x) (num y)). (* Sadly we need to give the arguments. TODO: Extend tactics to work with terms containing evars *)
    frewrite IHx. apply num_add_homomorphism'.
Qed.




(* Rewrite under quantors: *)

Goal forall t t', FA ⊢ (t == t') -> FA ⊢ ∀ $0 ⊕ σ t`[↑] == t' ⊕ σ $0.
Proof.
  intros. frewrite H. 
Abort.

Goal forall t t', FA ⊢ (t == t') -> FA ⊢ ∀∃ $0 ⊕ σ t == t'`[↑]`[↑] ⊕ σ $0.
Proof.
  intros. frewrite <- H. 
Abort.






(** Classical logic *)

Goal forall phi, [] ⊢C (phi ∨ (phi --> ⊥)).
Proof.
  intro. fstart. fclassical phi.
  - fleft. fapply "H".
  - fright. fapply "H".
Qed.

Goal forall phi, [] ⊢C (((phi --> ⊥) --> ⊥) --> phi).
Proof.
  intro. fstart. fintros. fcontradict as "X". fapply "H". fapply "X".
Qed.




(** Theories *)

Definition TFA phi := phi el FA.

Lemma num_add_homomorphism_T x y :
  TFA ⊩ (num x ⊕ num y == num (x + y)).
Proof.
  induction x; cbn.
  - fapply ax_add_zero.
  - fstart. frewrite <- IHx. fapply ax_add_rec.
Qed.

Definition TFA_ind : theory := fun phi => phi el FA \/ exists psi, phi = PA_induction psi.

Lemma add_zero_right :
  TFA_ind ⊩ ∀ $0 ⊕ zero == $0.
Proof.
  fstart. assert (TFA_ind ⊩ PA_induction ($0 ⊕ zero == $0)) as H.
  { apply Ctx. right. now eexists. }
  unfold PA_induction in H. fapply H; clear H.
  - fapply ax_add_zero.
  - fassert ax_trans as "trans". ctx.
    fassert ax_add_rec as "add_rec". ctx.
    fassert ax_eq_succ as "eq_succ". ctx.
    fintros "x" "IH". feapply "trans".
    + fapply "add_rec".
    + fapply "eq_succ". fapply "IH".
Qed.




(** XM for closed, quantor free formulas: *)

Lemma eq_num t :
  bound_term 0 t = true -> exists n, FA ⊢ (t == num n).
Proof.
  intros H0. induction t.
  - now exfalso.
  - destruct F; repeat depelim v; cbn in H0.
    + exists 0. fapply ax_refl.
    + destruct (IH h) as [n H]. left. now destruct (bound_term 0 h).
      exists (S n). cbn. now fapply ax_eq_succ.
    + destruct (IH h) as [n1 H1]. left. now destruct (bound_term 0 h).
      destruct (IH h0) as [n2 H2]. right. left. now do 2 destruct bound_term.
      exists (n1 + n2). assert (H := num_add_homomorphism n1 n2). frewrite <- H.
      now fapply ax_eq_add.
    + destruct (IH h) as [n1 H1]. left. now destruct (bound_term 0 h).
      destruct (IH h0) as [n2 H2]. right. left. now do 2 destruct bound_term.
      exists (n1 * n2). assert (H := num_mult_homomorphism n1 n2). frewrite <- H.
      now fapply ax_eq_mult.
Qed.

Fixpoint quantor_free (phi : form) := match phi with
| fal => True
| atom _ _ => True
| bin _ phi1 phi2 => quantor_free phi1 /\ quantor_free phi2
| quant _ _ => False
end.

Lemma xm_quantor_free phi :
  closed phi = true -> quantor_free phi -> (ax_zero_succ::ax_succ_inj::FA) ⊢ (phi ∨ (phi --> ⊥)).
Proof.
  intros H0 H1. induction phi; fstart.
  - fright. fintros "F". fapply "F".
  - destruct P. repeat depelim v. cbn in H0, H1. clear H1. 
    destruct (eq_num h) as [n1 H1]. now destruct bound_term.
    destruct (eq_num h0) as [n2 H2]. now do 2 destruct bound_term.
    frewrite H1. frewrite H2. clear H1 H2. 
    fstop; revert n2; induction n1 as [|n1 IH]; intros; fstart; cbn.
    + destruct n2; cbn.
      * fleft. fapply ax_refl.
      * fright. fapply ax_zero_succ.
    + destruct n2; cbn.
      * fright. fintros. feapply ax_zero_succ. feapply ax_sym. ctx.
      * specialize (IH n2). fdestruct IH as "[IH|IH]".
        -- fleft. frewrite "IH". fapply ax_refl.
        -- fright. fintro. fapply "IH". fapply ax_succ_inj. ctx.
  - cbn in H0, H1. destruct (bound 0 phi1) eqn:H2. 2: now exfalso.
    fassert (phi1 ∨ (phi1 --> ⊥)) as "IH1" by now fapply IHphi1.
    fassert (phi2 ∨ (phi2 --> ⊥)) as "IH2" by now fapply IHphi2.
    destruct b.
    + fdestruct "IH1" as "[IH1|IH1]". fdestruct "IH2" as "[IH2|IH2]".
      * fleft. fsplit; ctx.
      * fright. fintros "[ ]". fapply "IH2". ctx.
      * fright. fintros "[ ]". fapply "IH1". ctx.
    + fdestruct "IH1" as "[IH1|IH1]". 2: fdestruct "IH2" as "[IH2|IH2]".
      * fleft. fleft. ctx.
      * fleft. fright. ctx.
      * fright. fintros "[|]". fapply "IH1"; ctx. fapply "IH2"; ctx.
    + fdestruct "IH1" as "[IH1|IH1]". fdestruct "IH2" as "[IH2|IH2]".
      * fleft. fintro. ctx.
      * fright. fintro "H1". fapply "IH2". fapply "H1". ctx.
      * fleft. fintro. fexfalso. fapply "IH1". ctx.
  - now exfalso.
Qed.




(** Attempted Leibniz proof *)

Lemma leibniz_term (t t' s : term) :
  FA ⊢ (t == t' --> s`[t..] == s`[t'..]).
Proof.
  fintros. induction s; cbn.
  - destruct x; cbn. ctx. fapply ax_refl.
  - destruct F; repeat depelim v; cbn.
    * fapply ax_refl.
    * fapply ax_eq_succ. apply IH. left.
    * fapply ax_eq_add; apply IH. left. right. left.
    * fapply ax_eq_mult; apply IH. left. right. left.
Qed.

Lemma leibniz A phi t t' :
  FA <<= A -> A ⊢ (t == t') -> A ⊢ phi[t..] -> A ⊢ phi[t'..].
Proof.
  intros X. revert t t'. 
  enough (forall t t', A ⊢ (t == t') -> A ⊢ (phi[t..] --> phi[t'..])) as H0.
  { intros. specialize (H0 t t' H). fapply (H0 H1). }
  induction phi; cbn; intros. 1-3: fintros.
  - ctx.
  - destruct P. repeat depelim v. cbn in *. feapply ax_trans.
    + feapply ax_trans. pose (leibniz_term t' t h) as H'. 
      fapply H'. fapply ax_sym. fapply H. ctx.
    + pose (leibniz_term t t' h0) as H'. fapply H'. fapply H.
  - destruct b. 1,2: specialize (IHphi1 t t' H); specialize (IHphi2 t t' H).
    + fsplit. 
      * fapply IHphi1. fdestruct 0. ctx. 
      * fapply IHphi2. fdestruct 0. ctx.
    + fdestruct 0. 
      * fleft. fapply IHphi1. ctx.
      * fright. fapply IHphi2. ctx.
    + fintros. specialize (IHphi2 t t' H). fapply IHphi2. 
      fapply 1. assert (A ⊢ (t' == t)) as H' by now fapply ax_sym.
      specialize (IHphi1 t' t H'). fapply IHphi1. ctx.
  - destruct q.
    + 
Admitted.




(** Division Theorem with Hoas *)

Ltac custom_fold ::= fold zero in *; fold PA_induction in *.
Ltac custom_unfold ::= unfold zero in *; unfold PA_induction in *.

Require Import Hoas.

Notation "'σ' x" := (@bFunc PA_funcs_signature Succ (Vector.cons bterm x 0 (Vector.nil bterm))) (at level 37) : hoas_scope.
Notation "x '⊕' y" := (@bFunc PA_funcs_signature Plus (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (@bFunc PA_funcs_signature Mult (Vector.cons x (Vector.cons y (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (@bAtom PA_funcs_signature PA_preds_signature _ Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.


(* FA enriched with the neccessary induction rules to prove the division theorem *)
Definition FAI := 
  PA_induction (∀ (∃ (∃ $3 == $0 ⊕ $1 ⊗ σ $2 ∧ (∃ $1 ⊕ $0 == $3)))) :: 
  PA_induction (∀ $1 == $0 ∨ ($1 == $0 --> ⊥)) :: 
  PA_induction (zero == $0 ∨ (zero == $0 --> ⊥)) ::
  ∀ PA_induction (σ $1 == $0 ∨ (σ $1 == $0 --> ⊥)) ::
  PA_induction (∀ (∃ (∃ $3 == $0 ⊕ $1 ⊗ σ $2 ∧ (∃ $1 ⊕ $0 == $3)))) ::
  PA_induction (∀ (∀ ($1 == $0 --> ⊥) --> $1 ⊕ $2 == $0 --> (∃ σ $2 ⊕ $0 == $1))) ::
  PA_induction (∀ $1 ⊕ σ $0 == σ ($1 ⊕ $0)) ::
  PA_induction (∀ $1 ⊕ $0 == $0 ⊕ $1) ::
  PA_induction ($0 ⊕ zero == $0) ::
  ax_zero_succ ::
  ax_succ_inj ::
  FA.


Definition leq a b := (∃' k, a ⊕ k == b)%hoas.
Infix "≤" := leq (at level 45).


Lemma add_zero_r :
  FAI ⊢ <<(∀' x, x ⊕ zero == x)%hoas.
Proof.
  fstart. fapply ((PA_induction ($0 ⊕ zero == $0))).
  - frewrite (ax_add_zero zero). fapply ax_refl.
  - fintros "x" "IH". frewrite (ax_add_rec zero x). frewrite "IH". fapply ax_refl.
Qed. 

Lemma add_succ_r :
  FAI ⊢ <<(∀' x y, x ⊕ σ y == σ (x ⊕ y))%hoas.
Proof.
  fstart. fapply ((PA_induction (∀ $1 ⊕ σ $0 == σ ($1 ⊕ $0)))).
  - fintros "y". frewrite (ax_add_zero (σ y)). frewrite (ax_add_zero y). fapply ax_refl.
  - fintros "x" "IH" "y". frewrite (ax_add_rec (σ y) x). frewrite ("IH" y). 
    frewrite (ax_add_rec y x). fapply ax_refl.
Qed.

Lemma add_comm :
  FAI ⊢ <<(∀' x y, x ⊕ y == y ⊕ x)%hoas.
Proof.
  fstart. fapply ((PA_induction (∀ $1 ⊕ $0 == $0 ⊕ $1))).
  - fintros. frewrite (ax_add_zero x). frewrite (add_zero_r x). fapply ax_refl.
  - fintros "x" "IH" "y". frewrite (add_succ_r y x). frewrite <- ("IH" y).
    frewrite (ax_add_rec y x). fapply ax_refl.
Qed.

Lemma term_eq_dec :
  FAI ⊢ <<(∀' x y, (x == y) ∨ (x == y --> ⊥))%hoas.
Proof.
  fstart. fapply ((PA_induction (∀ $1 == $0 ∨ ($1 == $0 --> ⊥)))).
  - fapply ((PA_induction (zero == $0 ∨ (zero == $0 --> ⊥)))).
    + fleft. fapply ax_refl.
    + fintros "x" "IH". fright. fapply ax_zero_succ. 
  - fintros "x" "IH". fapply ((∀ PA_induction (σ $1 == $0 ∨ (σ $1 == $0 --> ⊥)))).
    + fright. fintros "H". feapply ax_zero_succ. feapply ax_sym. fapply "H".
    + fintros "y" "IHy". fspecialize ("IH" y). fdestruct "IH" as "[IH|IH]".
      * fleft. frewrite "IH". fapply ax_refl.
      * fright. fintros "H". fapply "IH". fapply ax_succ_inj. fapply "H".
Qed.

Lemma neq_le :
  FAI ⊢ <<(∀' k r y, (r == y --> ⊥) --> (r ⊕ k == y) --> ∃' k', σ r ⊕ k' == y)%hoas.
Proof.
  fstart. fapply ((PA_induction (∀ (∀ ($1 == $0 --> ⊥) --> $1 ⊕ $2 == $0 --> (∃ σ $2 ⊕ $0 == $1))))).
  - fintros "r" "y" "H1" "H2". fexfalso. fapply "H1". frewrite <- (ax_add_zero r).
    frewrite (add_comm zero r). ctx.
  - fintros "k" "IH" "r" "y". fintros "H1" "H2". fexists k.
    frewrite <- "H2". frewrite (ax_add_rec k r). frewrite (add_comm r (σ k)).
    frewrite (ax_add_rec r k). frewrite (add_comm k r). fapply ax_refl.
Qed.

Lemma division_theorem :
  FAI ⊢ <<(∀' x y, ∃' q r, (x == r ⊕ q ⊗ σ y) ∧ (r ≤ y))%hoas.
Proof.
  fstart. fapply ((PA_induction (∀ (∃ (∃ $3 == $0 ⊕ $1 ⊗ σ $2 ∧ (∃ $1 ⊕ $0 == $3)))))).
  - fintros "y". fexists zero. fexists zero. fsplit.
    + frewrite (ax_mult_zero (σ y)). frewrite (ax_add_zero zero). fapply ax_refl.
    + fexists y. fapply ax_add_zero.
  - fintros "x" "IH" "y". fspecialize ("IH" y). fdestruct "IH" as "[q [r [IH1 [k IH2]]]]".
    fassert (r == y ∨ (r == y --> ⊥)) as "[H|H]" by fapply term_eq_dec.
    + fexists (σ q). fexists zero. fsplit.
      * frewrite (ax_add_zero (σ q ⊗ σ y)). frewrite (ax_mult_rec q (σ y)).
        frewrite (ax_add_rec (q ⊗ σ y) y). fapply ax_eq_succ.
        frewrite "IH1". frewrite "H". fapply ax_refl.
      * fexists y. fapply ax_add_zero.
    + fexists q. fexists (σ r). fsplit.
      * frewrite (ax_add_rec (q ⊗ σ y) r). fapply ax_eq_succ. ctx.
      * fapply (neq_le k r y). ctx. ctx.
Qed.



