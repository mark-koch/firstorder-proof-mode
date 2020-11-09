Require Import Tarski.
Require Import List.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).

Ltac comp := repeat (progress (cbn in *; autounfold in *)).

Inductive peirce := class | intu.
Existing Class peirce.

Section ND_def.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Reserved Notation "A ⊢ phi" (at level 61).
  
  (** ** Definition *)

  Implicit Type p : peirce.

  Inductive prv : forall (p : peirce), list (form) -> form -> Prop :=
  | II {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi
  | IE {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi
  | AllI {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi
  | AllE {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..]
  | ExI {p} A t phi : A ⊢ phi[t..] -> A ⊢ ∃ phi
  | ExE {p} A phi psi : A ⊢ ∃ phi -> phi::(map (subst_form ↑) A) ⊢ psi[↑] -> A ⊢ psi
  | Exp {p} A phi : prv p A ⊥ -> prv p A phi
  | Ctx {p} A phi : phi el A -> A ⊢ phi
  | CI {p} A phi psi : A ⊢ phi -> A ⊢ psi -> A ⊢ phi ∧ psi
  | CE1 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ phi
  | CE2 {p} A phi psi : A ⊢ phi ∧ psi -> A ⊢ psi
  | DI1 {p} A phi psi : A ⊢ phi -> A ⊢ phi ∨ psi
  | DI2 {p} A phi psi : A ⊢ psi -> A ⊢ phi ∨ psi
  | DE {p} A phi psi theta : A ⊢ phi ∨ psi -> phi::A ⊢ theta -> psi::A ⊢ theta -> A ⊢ theta
  | Pc A phi psi : prv class A (((phi --> psi) --> phi) --> phi)
  where "A ⊢ phi" := (prv _ A phi).

  Arguments prv {_} _ _.

  Hint Constructors prv : core.

  Notation "A ⊢ phi" := (prv A phi) (at level 61).
  Notation "A ⊢C phi" := (@prv class A phi) (at level 30).
  Notation "A ⊢I phi" := (@prv intu A phi) (at level 30).

  Section Weakening.

    Context {p : peirce}.

    Lemma incl_map X Y (f : X -> Y) A B :
      A <<= B -> map f A <<= map f B.
    Proof.
      induction A; cbn.
      - firstorder.
      - intros H x [<-|H'].
        + apply in_map, H. now left.
        + firstorder.
    Qed.

    Lemma incl_right X (A B : list X) x :
      A <<= B -> x::A <<= x::B.
    Proof.
      firstorder.
    Qed.

    Theorem Weak A B phi :
      A ⊢ phi -> A <<= B -> B ⊢ phi.
    Proof.
      intros H. revert B.
      induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
    Qed.
    
    Theorem subst_Weak A phi xi :
      A ⊢ phi -> map (subst_form xi) A ⊢ phi[xi].
    Proof.
      induction 1 in xi |-*; comp.
      1-2,7-15: eauto using in_map.
      - apply AllI. setoid_rewrite map_map in IHprv. erewrite map_map, map_ext.
        apply IHprv. intros ?. comp. admit.
      - specialize (IHprv xi). apply AllE with (t0 := t [xi]) in IHprv. admit.
      - specialize (IHprv xi). eapply ExI with (t0 := t [xi]). admit.
      - eapply ExE in IHprv1. eassumption. rewrite map_map.
        specialize (IHprv2 (up xi)). erewrite <- up_form.
        erewrite map_map, map_ext in IHprv2. apply IHprv2.
        apply up_form.
    Admitted.
    
  End Weakening.

  Section ShiftContext.

    Context {p : peirce}.
    
    (* Fixpoint Conj A := match A with *)
    (*                       | nil => ⊥ --> ⊥ *)
    (*                       | phi::L => phi ∧ Conj L *)
    (*                       end. *)


    Fixpoint Conj A := match A with
                          | nil => ⊥ --> ⊥
                          | phi::L => match L with
                                   | nil => phi
                                   | _ :: _ => phi ∧ Conj L
                                   end
                          end.


        
    Lemma switch_conj_imp alpha beta phi A : A ⊢ alpha ∧ beta --> phi <-> A ⊢ alpha --> beta --> phi.
    Proof.
      split; intros H.
      - apply II, II. eapply IE.
        apply (Weak A). apply H. firstorder.
        apply CI; apply Ctx; firstorder.
      - apply II. apply (IE _ beta). apply (IE _ alpha).
        eapply Weak. apply H.
        firstorder.
        eapply CE1, Ctx; firstorder.
        eapply CE2, Ctx; firstorder.
    Qed.


    Lemma switch_imp A alpha phi : A ⊢ alpha --> phi <-> alpha::A ⊢ phi.
    Proof.
      split.
      - intros H. eapply IE. 2: apply Ctx. eapply Weak.
        exact H. all : firstorder.
      - apply II.
    Qed.


    Lemma conj_comm A alpha beta phi : alpha ∧ beta :: A ⊢ phi -> beta ∧ alpha :: A ⊢ phi.
    Proof.
      intros H%switch_imp. eapply IE. apply (Weak A).
      apply H. firstorder. apply CI.
      all: apply switch_imp, switch_conj_imp, II, II, Ctx; firstorder.
    Qed.
        
    
    Lemma shift_context A : forall phi, A ⊢ phi <-> nil ⊢ (Conj A) --> phi.
    Proof.
      induction A.
      - split; intros H.
        + apply II. eapply Weak. apply H. firstorder.
        + eapply IE. apply H. cbn. apply II. apply Ctx; firstorder.
      - intros phi. cbn. rewrite <-switch_imp, IHA, <-switch_conj_imp.
        destruct A.
        + cbn. rewrite switch_conj_imp. split; intros H.
          ++ eapply IE. apply H. apply II, Ctx. firstorder.
          ++ rewrite switch_imp. eapply Weak. apply H. firstorder.
        + split; intros; apply II.
        all: now apply conj_comm, switch_imp.
    Qed.
    
    
  End ShiftContext.
  
  
End ND_def.


Hint Constructors prv : core.

Arguments prv {_ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A ⊢C phi" := (@prv _ _ class A phi) (at level 30).
Notation "A ⊢I phi" := (@prv _ _ intu A phi) (at level 30).

Section Theories.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Definition theory := form -> Prop.
  Definition in_theory (T : theory) phi := T phi.

End Theories.

Notation "phi ∈ T" := (in_theory T phi) (at level 70).
Notation "A ⊏ T" := (forall phi, phi el A -> phi ∈ T) (at level 70).
Definition tprv {sig1 sig2 p} T phi := (exists A, A ⊏ T /\ @prv sig1 sig2 p A phi).

Notation "T ⊩ phi" := (tprv T phi) (at level 30).
Notation "T ⊩C phi" := (@tprv _ _ class T phi) (at level 30).
Notation "T ⊩I phi" := (@tprv _ _ intu T phi) (at level 60).

Section Soundness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Definition valid A phi :=
    forall D (I : interp D) rho, (forall Phi, Phi el A -> rho ⊨ Phi) -> rho ⊨ phi.

  Lemma Soundness A phi :
    A ⊢I phi -> valid A phi.
  Proof.
    remember intu as p.
    induction 1; intros D I rho HA; comp.
    - intros Hphi. apply IHprv; trivial. intros ? []; subst. assumption. now apply HA.
    - now apply IHprv1, IHprv2.
    - intros d. apply IHprv; trivial. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Heqp D I rho HA (eval rho t)). now intros [].
    - exists (eval rho t). cbn. specialize (IHprv Heqp D I rho HA).
      apply sat_comp in IHprv. eapply sat_ext; try apply IHprv. now intros [].
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el map (subst_form ↑) A -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Heqp D I (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - apply (IHprv Heqp) in HA. firstorder.
    - firstorder.
    - firstorder.
    - firstorder. now apply H0.
    - firstorder. now apply H0.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - discriminate.
  Qed.

  Definition tvalid T phi :=
    forall D (I : interp D) rho, (forall phi, phi ∈ T -> rho ⊨ phi) -> rho ⊨ phi.

  Lemma tSoundness T phi :
    T ⊩I phi -> tvalid T phi.
  Proof.
    intros (A & HA1 & HA2) D I rho HT. eapply Soundness in HA2; eauto.
  Qed.

End Soundness.
