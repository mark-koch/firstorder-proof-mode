Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import List.
Require Import Lia.

(* I follow the treatment of Peter Smith in "Introduction to Gödel's Theorems"
 (page 37) *)


(* Define the non-logical symbols used in the language of PA *)

Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Inductive PA_preds : Type :=
  Eq : PA_preds.

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | Eq => 2
end.


Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.

 
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Definition zero := func Zero (Vector.nil term).
Notation "'σ' x" := (func Succ (Vector.cons x (Vector.nil term))) (at level 37).
Notation "x '⊕' y" := (func Plus (Vector.cons x (Vector.cons y (Vector.nil term))) ) (at level 39).
Notation "x '⊗' y" := (func Mult (Vector.cons x (Vector.cons y (Vector.nil term))) ) (at level 38).
Notation "x '==' y" := (atom Eq (Vector.cons term x 1 (Vector.cons term y 0 (Vector.nil term))) ) (at level 40).



Fixpoint num n :=
  match n with
    O => zero
  | S x => σ (num x)
  end.

                      


(* formulate axioms of PA (see page 92) *)

Definition ax_zero_succ := ∀    zero == σ var 0 --> fal.
Definition ax_succ_inj :=  ∀ ∀  σ $1 == σ $0 --> $1 == $0.
Definition ax_add_zero :=  ∀    zero ⊕ $0 == $0.
Definition ax_add_rec :=   ∀ ∀  (σ $0) ⊕ $1 == σ ($0 ⊕ $1).
Definition ax_mult_zero := ∀    zero ⊗ $0 == zero.
Definition ax_mult_rec :=  ∀ ∀  σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0.

Definition PA_induction (phi : form) :=
  phi[zero..] --> (∀ phi --> phi[σ $0 .: S >> var]) --> ∀ phi.

Definition phi := $0 == $1.

Compute (phi[zero..]).
Compute (phi[zero .: S >> var]).

(* substitutes t for the variable $0 and leaves all other variables unchanged *)
Definition var0_subst (t : term) : nat -> term :=
  fun n => match n with 0 => t | S n => var (S n) end.


(* var0_subst can be expressed with scons and funcomp *)
Lemma var0_subst_spec t n :
  var0_subst t n = (t .: S >> var) n.
Proof.
  now destruct n as [].
Qed.



                                              

(*** Working in models of PA ***)
                                              
Section Models.                                              
  

  Variable D : Type.
  Variable I : interp D.

  Definition Equality := forall v, @i_P _ _ D I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v). 
  Hypothesis equality : forall v, @i_P _ _ D I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v).

  (* The following predicate expresses that a model satisfies the minimal axioms of PA i.e. all axioms except S x <> 0 *)
  Definition sat_PA_minimal_axioms :=
    forall rho,
      rho ⊨ ax_succ_inj
      /\ rho ⊨ ax_add_zero
      /\ rho ⊨ ax_add_rec
      /\ rho ⊨ ax_mult_zero
      /\ rho ⊨ ax_mult_rec
      /\ (forall phi, rho ⊨ (PA_induction phi) ).      


  Definition sat_PA_axioms :=
    sat_PA_minimal_axioms /\ forall rho, rho ⊨ ax_zero_succ.




  
  Lemma PAeq_sym : forall rho a b, rho ⊨ (a == b) -> rho ⊨ (b == a).
  Proof.
    intros rho a b H. apply equality; cbn. apply equality in H; cbn in H. auto.
  Qed.
  
  Lemma PAeq_trans : forall rho a b c, rho ⊨ (a == b) /\ rho ⊨ (b == c) -> rho ⊨ (a == c).
  Proof.
    intros rho a b c. cbn. rewrite !equality. cbn. intros [C B]. now rewrite C, B.
  Qed.

  Definition iO := i_f (f:=Zero) (Vector.nil D).
  Notation "'iσ' d" := (i_f (f:=Succ) (Vector.cons d (Vector.nil D))) (at level 37).
  Notation "x 'i⊕' y" := (i_f (f:=Plus) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 39).
  Notation "x 'i⊗' y" := (i_f (f:=Mult) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 38).
  Definition iμ k := iter (fun x => iσ x) k iO.



  (* provide all axioms in a more useful form *)
  Theorem succ_inj:
    (forall rho, rho ⊨ ax_succ_inj) -> forall n d, iσ d = iσ n -> d = n.
  Proof.
    intros H n d. specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.

  Theorem add_zero :
    (forall rho, rho ⊨ ax_add_zero) -> forall d, iO i⊕ d = d.
  Proof.
    intros H d. specialize (H (fun _ => iO) d).
    cbn in H. rewrite equality in H; now cbn in H.
  Qed.

  Theorem add_rec :
    (forall rho, rho ⊨ ax_add_rec) -> forall n d, (iσ n) i⊕ d = iσ (n i⊕ d). 
  Proof.
    intros H n d.
    specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.
      
  Theorem mult_zero :
    (forall rho, rho ⊨ ax_mult_zero) -> forall d, iO i⊗ d = iO.
  Proof.
    intros H d. specialize (H (fun _ => iO) d).
    cbn in H. rewrite !equality in H. now cbn in H.
  Qed.

  Theorem mult_rec :
    (forall rho, rho ⊨ ax_mult_rec) -> forall n d, (iσ d) i⊗ n = n i⊕ (d i⊗ n).
  Proof.
    intros H n d. specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.

  
  Variable AX : sat_PA_minimal_axioms.
  
  
  Theorem PAinduction_weak (phi : form) rho :
    rho ⊨ phi[zero..] -> rho ⊨ (∀ phi --> phi[σ $ 0 .: S >> var]) -> rho ⊨ (∀ phi).
  Proof.
    destruct (AX rho) as (_&_&_&_&_&H). cbn. apply (H phi).
  Qed.
  
  
  Definition null := (fun _ : nat => iO).
  Definition representable (P : D -> Prop) := exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.

  Lemma sat_single (rho : nat -> D) (Phi : form) (t : term) :
    (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
  Proof.
    rewrite sat_comp. apply sat_ext. now intros [].
  Qed.

  (** Useful induction principle *)
  
  Theorem PAinduction (P : D -> Prop) :
    representable P -> P iO -> (forall d, P d -> P (iσ d)) -> forall d, P d.
  Proof.
    intros (phi & rho & repr) P0 IH. intros d. rewrite repr.
    apply PAinduction_weak.
    - apply sat_single. apply repr. apply P0.
    - cbn. intros d' H. apply repr, IH, repr in H.
      apply sat_comp. eapply sat_ext; try apply H. now intros [].
  Qed.

  (** Examples *)

  Lemma add_exists : forall (phi : form) rho, rho ⊨ phi -> exists sigma, sigma ⊨ (∃ phi).
  Proof.
    intros phi rho H; cbn. exists (fun n => match n with
                           | O => rho 1
                           | S m => rho (S n)
                                end); exists (rho 0).
    unfold scons. eapply sat_ext; try apply H. now intros [|[|]].
  Qed.

  Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.
  
  Lemma add_n_exists : forall n,
      forall (phi : form) rho, rho ⊨ phi -> exists sigma, sigma ⊨ (exist_times n phi).
  Proof.
    induction n; intros phi rho H.
    - exists rho. auto. 
    - destruct (IHn _ _ H) as [s Hs]. now refine (add_exists _ s _).
  Qed.
  
  Lemma zero_or_succ : forall rho, rho ⊨ (∀ zero == $0 ∨ ∃ $1 == σ $0).
  Proof.
    intros rho. apply PAinduction_weak.
    - left. now apply equality.
    - intros d _. right. exists d; now apply equality.
  Qed.


  Goal forall d, iO = d \/ exists x, d = iσ x. 
  Proof.
    enough (forall rho, rho ⊨ (∀ zero == $0 ∨ ∃ $1 == σ $0)) as H. intros d.
    specialize (H null). cbn in H. specialize (H d). revert H.
    rewrite equality. cbn.
    intros [<- | [x H]]. now left. right. rewrite equality in H. now exists x.
    apply zero_or_succ.
  Qed.

  Goal forall d, iO = d \/ exists x, d = iσ x. 
  Proof.
    apply PAinduction.
    pose (phi := zero == $0 ∨ ∃ $1 == σ $0).
    - exists phi, (fun _ => iO). split.
      + intros [<- | [x ->]].
        * left. cbn. now rewrite equality.
        * right. exists x. cbn. now rewrite equality.
      + intros [H | [x H]].
        * left. cbn in H. now rewrite equality in H.
        * right. exists x. cbn in H. now rewrite equality in H.
    - now left.
    - intros d [<- |]; right. now exists iO. now exists d.
  Qed.

  Lemma add_rec_right :
    forall d n, n i⊕ (iσ d) = iσ (n i⊕ d).
  Proof.
    intros n. apply PAinduction.
    - pose (phi := ∀ $0 ⊕ σ $1 == σ ($0 ⊕ $1) ).
      exists phi, (fun _ => iO). admit.
    - rewrite !add_zero; try reflexivity. all: firstorder.
    - intros d IH. rewrite !add_rec. now rewrite IH. all: firstorder.
  Admitted.
    
  
  
  
  Section TrivialModel.

    Variable Bot : iμ 0 = iμ 1.
    
    Lemma ModelHasOnlyZero' rho : rho ⊨ (∀ $0 == zero).
    Proof.
      apply PAinduction_weak.
      - cbn; now apply equality.
      - cbn. fold iO. intros d. rewrite !equality; cbn. intros IH.
        now rewrite IH. 
    Qed.

    
    Fact ModelHasOnlyZero : forall d, d = iO.
    Proof.
      apply PAinduction.
      pose (phi := $0 == zero).
      - exists phi, (fun _ => iO). split.
        + intros ->. cbn. now rewrite equality.
        + intros H. cbn in H. now rewrite equality in H.
      - reflexivity.
      - intros d. now intros ->.
    Qed.

    
    Lemma trivial_induction' rho phi : rho ⊨ (phi[zero..] --> ∀ phi).
    Proof.
      cbn. intros H0. apply PAinduction_weak.
      - exact H0.
      - cbn. intros d IH. apply sat_comp.
        refine (@sat_ext' _ _ _ _ (d.:rho) _ phi _ _).
        destruct x; cbn; rewrite ModelHasOnlyZero; apply ModelHasOnlyZero.
        exact IH.
    Qed.
      
    
    Fact trivial_induction : forall P, representable P -> P iO -> forall d, P d.
    Proof.
      intros P Rep P0. apply PAinduction; try auto.
      intros. now rewrite ModelHasOnlyZero.  
    Qed.
    
         
  End TrivialModel.
 
End Models.

                           









(*** Working with a Deduction System ***)

Section ND.

  Variable p : peirce.
  Definition FA' := ax_add_zero::ax_add_rec::ax_mult_zero::ax_mult_rec::nil.

  Definition ax_refl := (∀ $0 == $0).
  Definition ax_sym := (∀ ∀ $0 == $1 --> $1 == $0).
  Definition ax_trans := (∀∀∀ $0 == $1 --> $1 == $2 --> $0 == $2).

  Definition ax_eq_succ := (∀∀ $0 == $1 --> σ $0 == σ $1).
  Definition ax_eq_add := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3).
  Definition ax_eq_mult := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3).

  Definition FA := ax_refl::ax_sym::ax_trans::ax_eq_succ::ax_eq_add::ax_eq_mult::FA'.

  Lemma numeral_subst_invariance : forall n rho, subst_term rho (num n) = num n.
  Proof.
    induction n.
    - reflexivity.
    - intros rho. cbn. now rewrite IHn.
  Qed.

  Lemma term_subst_invariance t : forall rho,
      bound_term 0 t = true -> subst_term rho t = t.
  Proof.
    induction t.
    - intros ? H. inversion H.
    - intros rho HB. cbn. f_equal.
      enough ( Vector.map (subst_term rho) v = Vector.map id v ) as eq.
      cbn in eq. rewrite eq at 1. now rewrite (Vector.map_id _ _).
      apply Vector.map_ext_in.
      intros x Hx. cbv [id]. apply IH.
      assumption. refine (bound_term_parts _ _).
      apply HB. now apply vec_map_In.
  Qed.

  Lemma FA_refl t :
    FA ⊢ (t == t).
  Proof.
    assert (FA ⊢ ax_refl). apply Ctx. firstorder.
    eapply AllE in H. cbn in H. apply H.
  Qed.

  Lemma FA_sym t t' :
    FA ⊢ (t == t') -> FA ⊢ (t' == t).
  Proof.
    intros H. assert (H' : FA ⊢ ax_sym). apply Ctx. firstorder.
    eapply (AllE _ t') in H'. cbn in H'. apply (AllE _ t) in H'. cbn in H'.
    change (FA ⊢ (t == t'[↑][t..] --> t'[↑][t..] == t)) in H'.
    rewrite subst_term_shift in H'. apply (IE _ _ _ H'), H.
  Qed.

  Lemma FA_sym' t t' :
    FA ⊢ (t == t') -> FA ⊢ (t' == t).
  Proof.
    intros H. assert (H' : FA ⊢ ax_sym). apply Ctx. firstorder.
    eapply (AllE _ t') in H'. cbn in H'.
    change (FA ⊢ (∀ $0 == t'[↑] --> t'[↑] == $0)) in H'.
    apply (AllE _ t) in H'.
    change (FA ⊢ (t == t'[↑][t..] --> t'[↑][t..] == t)) in H'.
    rewrite subst_term_shift in H'. apply (IE _ _ _ H'), H.
  Qed.
  

  Lemma FA_tran a b c :
    FA ⊢ (a == b) -> FA ⊢ (b == c) -> FA ⊢ (a == c).
  Proof.
    intros H1 H2. assert (H : FA ⊢ ax_trans). apply Ctx. firstorder.
    apply (AllE _ c) in H. cbn in H.
    change (FA ⊢ ∀∀ $0 == $1 --> $1 == c[↑][↑] --> $0 == c[↑][↑]) in H.
    apply (AllE _ b) in H. cbn in H.
    change (FA ⊢ ∀ $0 == b[↑] --> b[↑] == c[↑][↑][up b..] --> $0 == c[↑][↑][up b..]) in H.
    apply (AllE _ a) in H. cbn in H.
    change (FA ⊢ (a == b[↑][a..] --> b[↑][a..] == c[↑][↑][up b..][a..] --> a == c[↑][↑][up b..][a..])) in H.
    rewrite (up_term (c[↑])) in H. rewrite !subst_term_shift in H.

    enough (FA ⊢ (b == c --> a == c)) as H'. apply (IE _ _ _ H'), H2.
    apply (IE _ _ _ H), H1.
  Qed.

  (*
    Definition ax_zero_succ := ∀    zero == σ var 0 --> fal.
    Definition ax_succ_inj :=  ∀ ∀  σ $1 == σ $0 --> $1 == $0.
    Definition ax_add_zero :=  ∀    zero ⊕ $0 == $0.
    Definition ax_add_rec :=   ∀ ∀  (σ $0) ⊕ $1 == σ ($0 ⊕ $1).
    Definition ax_mult_zero := ∀    zero ⊗ $0 == zero.
    Definition ax_mult_rec :=  ∀ ∀  σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0.

    Definition ax_refl := (∀ $0 == $0).
    Definition ax_sym := (∀ ∀ $0 == $1 --> $1 == $0).
    Definition ax_trans := (∀∀∀ $0 == $1 --> $1 == $2 --> $0 == $2).

    Definition ax_eq_succ := (∀∀ $0 == $1 --> σ $0 == σ $1).
    Definition ax_eq_add := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3).
    Definition ax_eq_mult := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3).
  *)

  Lemma num_add_homomorphism x y :
    FA ⊢ (num x ⊕ num y == num (x + y)).
  Proof.
    induction x.
    - cbn. assert (H : FA ⊢ ax_add_zero). apply Ctx. firstorder.
      eapply AllE in H. apply H.
    - cbn. assert (H1 : FA ⊢ ax_add_rec). apply Ctx. firstorder.
      eapply (AllE _ (num y)) in H1. 
      eapply (AllE _ (num x)) in H1. 
      cbn in H1. rewrite !numeral_subst_invariance in H1.

      eapply FA_tran. exact H1.

      assert (H2 : FA ⊢ ax_eq_succ). apply Ctx. firstorder.
      eapply (AllE _ ?[b]) in H2. eapply (AllE _ ?[a]) in H2. cbn in H2.
      change (FA ⊢ (?a == ?b[↑][?a..] --> σ ?a == σ ?b[↑][?a..])) in H2.
      rewrite subst_term_shift in H2.

      eapply IE. exact H2. exact IHx.
  Qed.

  (* Lemma num_mult_homomorphism x y : FA ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
    induction x.
    - cbn. assert (H : FA ⊢ ax_mult_zero). apply Ctx. firstorder.
      eapply AllE in H. apply H.
    - cbn.
  Admitted.

  Lemma leibniz phi t t' :
    FA ⊢ (t == t') -> FA ⊢ phi[t..] -> FA ⊢ phi[t'..].
  Proof.
    intros H1 H2. induction H2 in |-*.
    - 
  Admitted. *)




End ND.
