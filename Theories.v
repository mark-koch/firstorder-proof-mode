Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import List.
Require Import Arith.PeanoNat.
From Equations Require Import Equations.
Require Import Coq.Logic.Eqdep_dec.



Definition subset_T `{funcs_signature, preds_signature} (T1 T2 : theory) := forall (phi : form), phi t∈ T1 -> phi t∈ T2.
Infix "⊑" := subset_T (at level 20).

Definition extend `{funcs_signature, preds_signature} T (phi : form) := fun psi => T psi \/ psi = phi.
Infix "⋄" := extend (at level 20).



Section Theories.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.

Context {p : peirce}.


Definition mapT (f : form -> form) (T : theory) : theory := fun phi => exists psi, T psi /\ f psi = phi.


(** Equality deciders *)

Context {eq_dec_Funcs : EqDec syms}.
Context {eq_dec_Preds : EqDec preds}.

Instance eqdec_vec X {DX : EqDec X} n : EqDec (Vector.t X n).
Proof.
  intros x y. apply Vector.eq_dec with (A_beq := fun a b => if DX a b then true else false). intros a b. now destruct (DX a b).
Qed.

Lemma eqdec_vec_in X n (v : vec X n) :
  (forall x, vec_in x v -> forall y, {x = y} + {x <> y}) -> forall v', {v = v'} + {v <> v'}.
Proof.
  intros Hv. induction v.
  - intros v'. dependent elimination v'. now left.
  - intros v'. dependent elimination v'. destruct (Hv h (vec_inB h v) h0) as [->|].
    destruct ((IHv (fun x H => Hv x (vec_inS x h0 v H))) t) as [->|]. now left.
    right. intros [=]. apply inj_pair2_eq_dec in H0. auto. intros x y. decide equality.
    right. congruence.
Qed.

Global Instance eqdec_term : EqDec term.
Proof.
  intros x. induction x.
  - destruct y. destruct (eq_dec x n) as [->|]. now left. right. congruence.
    right. congruence.
  - destruct y. right. congruence. destruct (eq_dec F f) as [->|].
    assert ({v = v0} + {v <> v0}) as [->|]. { apply eqdec_vec_in. exact X. }
    now left. right. intros [=]. apply inj_pair2_eq_dec in H0. auto. exact eq_dec.
    right. congruence.
Qed.

Global Instance eqdec_form : EqDec form.
Proof.
  intros x. induction x; destruct y; try (right; congruence).
  - now left.
  - destruct (eq_dec P P0) as [->|]. destruct (eq_dec v v0) as [->|].
    now left. right. intros [=]. apply inj_pair2_eq_dec in H0. auto. exact eq_dec.
    right. congruence.
  - destruct b, b0; try (right; congruence);
    destruct (IHx1 y1) as [->|], (IHx2 y2) as [->|]; try (now left); try (right; congruence).
  - destruct q, q0; try (right; congruence);
    destruct (IHx y) as [->|]; try (now left); try (right; congruence).
Qed.


(* Now we can define removal from formula lists *)
Definition rem := @remove form eq_dec.


(* Inductive unused_term (n : nat) : term -> Prop :=
| uft_var m : n <> m -> unused_term n ($m)
| uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (func F v).

Inductive unused (n : nat) : form -> Prop :=
| uf_Fal : unused n fal
| uf_Pred P v : (forall t, vec_in t v -> unused_term n t) -> unused n (atom P v)
| uf_Bin op phi psi : unused n phi -> unused n psi -> unused n (bin op phi psi)
| uf_Quant op phi : unused (S n) phi -> unused n (quant op phi).

Definition closed_theory (T : theory) := forall phi, phi t∈ T -> closed phi = true.

Lemma subst_closed s phi :
  closed phi = true -> phi[s] = phi.
Proof.
Admitted. *)


Theorem WeakT A B phi :
  A ⊩ phi -> A ⊑ B -> B ⊩ phi.
Proof.
  intros H. revert B.
  induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
Qed.


Lemma contains_nil T :
  List.nil ⊏ T.
Proof. intuition. now exfalso. Qed.

Lemma contains_cons a A T :
  a t∈ T -> A ⊏ T -> (a :: A) ⊏ T.
Proof. intros ? ? ? []; subst; intuition. Qed.

Lemma contains_cons2 a A T :
  (a :: A) ⊏ T -> A ⊏ T.
Proof. firstorder. Qed.

Lemma contains_app A B T :
  A ⊏ T -> B ⊏ T -> (A ++ B) ⊏ T.
Proof. intros ? ? ? [] % in_app_or; intuition. Qed.

Lemma contains_extend1 phi T :
  phi t∈ (T ⋄ phi).
Proof. now right. Qed.

Lemma contains_extend2 phi psi T :
  phi t∈ T -> phi t∈ (T ⋄ psi).
Proof. intros ?. now left. Qed.

Lemma contains_extend3 A T phi :
  A ⊏ T -> A ⊏ (T ⋄ phi).
Proof.
  intros ? ? ?. left. intuition.
Qed.



Lemma subset_refl T :
  T ⊑ T.
Proof.
  firstorder.
Qed.

Lemma subset_trans T1 T2 T3 :
  T1 ⊑ T2 -> T2 ⊑ T3 -> T1 ⊑ T3.
Proof.
  firstorder.
Qed.



Lemma contains_rem A T phi :
  A ⊏ T ⋄ phi -> rem phi A ⊏ T.
Proof.
  intros H1. induction A. firstorder. cbn. destruct (eq_dec phi a) as [->|H2].
  - apply IHA. eapply contains_cons2, H1.
  - apply contains_cons. destruct (H1 a) as [| ->]; firstorder. 
    apply IHA. eapply contains_cons2, H1.
Qed.

Lemma incl_rem1 A phi :
  rem phi A <<= A.
Proof.
  induction A. firstorder. cbn. destruct (eq_dec phi a) as [-> |]; firstorder.
Qed.

Lemma incl_rem2 A phi :
  A <<= phi :: rem phi A.
Proof.
  induction A. firstorder. cbn. destruct (eq_dec phi a) as [-> |]; firstorder.
Qed.




Definition shift_down := fun n => match n with 0 => $0 | S n => $n end.

Lemma map_shift_up_down_contains A T :
  (A ⊏ mapT (subst_form ↑) T) -> map (subst_form shift_down) A ⊏ T.
Proof.
  intros H1. induction A. easy. intros f H. destruct H as [<-|].
  - destruct (H1 a) as [f [H2 <-]]. now left. change (f[↑][shift_down] t∈ T). 
    enough (f[↑][shift_down] = f) as -> by easy. 
    rewrite subst_comp. now apply subst_id. 
  - firstorder.
Qed.

Lemma map_shift_up_down_eq A T :
  A ⊏ mapT (subst_form ↑) T -> map (subst_form ↑) (map (subst_form shift_down) A) = A.
Proof.
  intros H1. induction A. reflexivity. cbn. f_equal.
  - destruct (H1 a) as [f [H2 <-]]. now left.
    enough (f[↑ >> subst_term shift_down][↑] = f[↑]) as X by now rewrite <- subst_comp in X.
    f_equal. now apply subst_id.
  - firstorder.
Qed.




(** Prv translations *)

Lemma T_II T phi psi :
  T ⋄ phi ⊩ psi -> T ⊩ (phi --> psi).
Proof.
  intros [A[H1 H2]]. exists (rem phi A). split.
  intros ? ?%in_remove. firstorder.
  apply II. eapply Weak. apply H2. apply incl_rem2.
Qed.

Lemma T_IE T phi psi :
  T ⊩ (phi --> psi) -> T ⊩ phi -> T ⊩ psi.
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. exists (A++B). split.
  now apply contains_app. apply IE with phi. 
  eapply Weak. apply A2. now apply incl_appl.
  eapply Weak. apply B2. now apply incl_appr.
Qed.

Lemma T_AllI T phi :
  mapT (subst_form ↑) T ⊩ phi -> T ⊩ ∀ phi.
Proof.
  intros [A[H1 H2]].
  exists (map (subst_form shift_down) A). split.
  - now apply map_shift_up_down_contains.
  - apply AllI. erewrite map_shift_up_down_eq; auto.
Qed.

Lemma T_AllE T t phi :
  (T ⊩ ∀ phi) -> T ⊩ phi[t..].
Proof.
  intros [A[H1 H2]]. exists A. split. firstorder. now apply AllE.
Qed.

Lemma T_ExI T t phi :
  T ⊩ phi[t..] -> T ⊩ ∃ phi.
Proof.
  intros [A[A1 A2]]. exists A. split. firstorder. now apply ExI with t.
Qed.

Lemma T_ExE T phi psi :
  (T ⊩ ∃ phi) -> (mapT (subst_form ↑) T) ⋄ phi ⊩ psi[↑] -> T ⊩ psi.
Proof.
  intros [A[A1 A2]] [B[B1 B2]].
  exists (A ++ map (subst_form shift_down) (rem phi B)). split.
  - apply contains_app. assumption. apply map_shift_up_down_contains.
    now apply contains_rem.
  - eapply ExE.
    + eapply Weak. apply A2. now apply incl_appl.
    + eapply Weak. apply B2. rewrite map_app. erewrite map_shift_up_down_eq with (T := T).
      eapply incl_tran with (m := phi :: rem phi B). apply incl_rem2.
      apply incl_cons. now left. apply incl_tl. now apply incl_appr.
      clear B2. induction B. firstorder. cbn. destruct (eq_dec phi a) as [-> |].
      * firstorder.
      * apply contains_cons. destruct (B1 a) as [| ->]. now left. assumption.
        apply IHB. eapply contains_cons2, B1. easy. firstorder.
Qed.

Lemma T_Exp T phi :
  T ⊩ ⊥ -> T ⊩ phi.
Proof.
  intros [A[H1 H2]]. exists A. split. firstorder. now apply Exp.
Qed.

Lemma T_Ctx T phi :
  phi t∈ T -> T ⊩ phi.
Proof.
  intros H. exists (phi::nil). split.
  intros psi H2. now assert (phi = psi) as -> by firstorder.
  apply Ctx. now left.
Qed.

Lemma T_CI T phi psi :
  T ⊩ phi -> T ⊩ psi -> T ⊩ (phi ∧ psi).
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. exists (A++B). split.
  now apply contains_app. apply CI.
  eapply Weak. apply A2. now apply incl_appl.
  eapply Weak. apply B2. now apply incl_appr.
Qed.

Lemma T_CE1 T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi.
Proof.
  intros [A[H1 H2]]. exists A. split. assumption. eapply CE1. apply H2.
Qed.

Lemma T_CE2 T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ psi.
Proof.
  intros [A[H1 H2]]. exists A. split. assumption. eapply CE2. apply H2.
Qed.

Lemma T_DI1 T phi psi :
  T ⊩ phi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. exists A. split. assumption. eapply DI1. apply H2.
Qed.

Lemma T_DI2 T phi psi :
  T ⊩ psi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. exists A. split. assumption. eapply DI2. apply H2.
Qed.

Lemma T_DE T phi psi theta :
  T ⊩ (phi ∨ psi) -> T ⋄ phi ⊩ theta -> T ⋄ psi ⊩ theta -> T ⊩ theta.
Proof.
  intros [A[A1 A2]] [B[B1 B2]] [C[C1 C2]].
  exists (A ++ (rem phi B) ++ (rem psi C)). split.
  - apply contains_app. assumption. apply contains_app. 
    intros ? ?%in_remove. firstorder. intros ? ?%in_remove. firstorder.
  - eapply DE. eapply Weak. apply A2. now apply incl_appl.
    + eapply Weak. apply B2. apply incl_tran with (m := phi::rem phi B). 
      apply incl_rem2. apply incl_cons. now left.
      now apply incl_tl, incl_appr, incl_appl.
    + eapply Weak. apply C2. apply incl_tran with (m := psi::rem psi C). 
      apply incl_rem2. apply incl_cons. now left.
      now apply incl_tl, incl_appr, incl_appr.
Qed.

Lemma T_Pc T phi psi :
  T ⊩C (((phi --> psi) --> phi) --> phi).
Proof.
  exists nil. split. firstorder. apply Pc.
Qed.




Lemma switch_imp_T T alpha phi : T ⊩ (alpha --> phi) <-> (T ⋄ alpha) ⊩ phi.
Proof.
  split.
  - intros H. eapply T_IE. 2: apply T_Ctx. eapply WeakT.
    exact H. all : firstorder.
  - apply T_II.
Qed.


End Theories.
