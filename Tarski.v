Require Export FOL.
Require Import Lia.
Require Import Vector VectorTech.
Set Implicit Arguments.
Unset Strict Implicit.


(*** Full Syntax ***)

Inductive full_logic_sym : Type :=
| Conj : full_logic_sym
| Disj : full_logic_sym
| Impl : full_logic_sym.

Inductive full_logic_quant : Type :=
| All : full_logic_quant
| Ex : full_logic_quant.

Instance full_operators : operators :=
{| binop := full_logic_sym ; quantop := full_logic_quant |}.

Notation "∀ Phi" := (quant All Phi) (at level 50).
Notation "∃ Phi" := (quant Ex Phi) (at level 50).
Notation "A ∧ B" := (bin Conj A B) (at level 41).
Notation "A ∨ B" := (bin Disj A B) (at level 42).
Notation "A '-->' B" := (bin Impl A B) (at level 43, right associativity).



(*** Formula boundedness *)

Section Bound.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.


  

  
  
  (* this funtion yields true iff all variables that are used in the term are strictly smaller than k *)
  Fixpoint bound_term (k :nat) (t : term) : bool :=
    match t with
    | var n => if (Compare_dec.lt_dec n k) then true else false
    | func f v => andb_vec ( Vector.map (bound_term k) v ) 
    end.

  (* using the above, this function yields true iff all free variables are strictly smaller than k *)
  Fixpoint bound (k : nat) (phi : form) : bool :=
    match phi with
    | fal => true
    | atom P t => andb_vec (Vector.map (bound_term k) t)
    | bin op alpha beta => andb (bound k alpha) (bound k beta)
    | quant Q alpha => bound (S k) alpha
    end.


  Lemma bound_term_parts : forall B f tv, bound_term B (func f tv) = true ->
     (forall t', Vector.In (bound_term B t') (Vector.map (bound_term B) tv)
                                          -> bound_term B t' = true ). 
  Proof.
    intros N f tv HB t'. apply vec_true_entries, HB. 
  Qed.
  



  
  (* define closed formulas *)
  Definition closed (phi : form) := bound 0 phi.
  (* define predicates *)
  Definition predicate (phi : form) := bound 1 phi.
  
  Fixpoint iter {X: Type} f n (x : X) :=
    match n with
      0 => x
    | S m => f (iter f m x)
    end.
  
  Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.

  
  (* Gives the largest variable-number in a term *)
  Fixpoint max_term (t : term) :=
    match t with
    | $n => n
    | func f v => max_vec ( Vector.map max_term v )
    end.
  
  (* Gives the largest variable-number in a formula *)
  Fixpoint max_form (phi : form) :=
    match phi with
    | fal => 0
    | atom P t => max_vec (Vector.map max_term t ) 
    | bin op alpha beta => PeanoNat.Nat.max (max_form alpha) (max_form beta)
    | quant Q alpha => max_form alpha
    end.

  

  Lemma max_term_parts : forall B f tv, max_term (func f tv) <= B ->
     (forall t', Vector.In (max_term t') (Vector.map max_term tv)
                                          -> max_term t' <= B ). 
  Proof.
    intros N f tv HB t'. apply vec_max_entries, HB. 
  Qed.


  
  Lemma max_bin N alpha beta b :
    N < max_form (bin b alpha beta) <-> N < max_form alpha \/ N < max_form beta.
  Proof.
    destruct b; cbn; apply PeanoNat.Nat.max_lt_iff.
  Qed.

  Lemma max_quant phi Q : max_form (quant Q phi) = max_form phi.
  Proof.
    now cbn.
  Qed.
  
  
End Bound.



(*** Tarski Semantics ***)

Section Tarski.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  (** Semantic notions *)

  Section Semantics.

    Variable domain : Type.

    Class interp := B_I
      {
        i_f : forall f : syms, vec domain (ar_syms f) -> domain ;
        i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
      }.

    Definition env := nat -> domain.

    Context {I : interp }.
    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | var s => rho s
      | func f v => i_f (Vector.map (eval rho) v)
      end.

    Fixpoint sat (rho : env) (phi : form) : Prop :=
      match phi with
      | atom P v => i_P (Vector.map (eval rho) v)
      | fal => False
      | bin Impl phi psi => sat rho phi -> sat rho psi
      | bin Conj phi psi => sat rho phi /\ sat rho psi
      | bin Disj phi psi => sat rho phi \/ sat rho psi
      | quant Ex phi => exists d : domain, sat (d .: rho) phi
      | quant All phi => forall d : domain, sat (d .: rho) phi
      end.

  End Semantics.

  Notation "rho ⊨ phi" := (sat rho phi) (at level 20).
  
  Section Substs.
    
    Variable D : Type.
    Variable I : interp D.
    
    
    Lemma eval_ext rho xi t :
      (forall x, rho x = xi x) -> eval rho t = eval xi t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

    Lemma eval_comp rho xi t :
      eval rho (subst_term xi t) = eval (xi >> eval rho) t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

    Lemma sat_ext rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
    Proof.
      induction phi in rho, xi |- *; cbn; intros H.
      - reflexivity.
      - erewrite map_ext; try reflexivity. intros t. now apply eval_ext.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b; intuition.
      - destruct q.
        + split; intros H' d; eapply IHphi; try apply (H' d). 1,2: intros []; cbn; intuition.
        + split; intros [d H']; exists d; eapply IHphi; try apply H'. all: intros []; cbn; intuition.
    Qed.

    Lemma sat_ext' rho xi phi :
      (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
    Proof.
      intros Hext H. rewrite sat_ext. exact H.
      intros x. now rewrite (Hext x).
    Qed.

    Lemma sat_comp rho xi phi :
      rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
    Proof.
      induction phi in rho, xi |- *; cbn.
      - reflexivity.
      - erewrite map_map, map_ext; try reflexivity. intros t. apply eval_comp.
      - specialize (IHphi1 rho xi). specialize (IHphi2 rho xi). destruct b; intuition.
      - destruct q.
        + setoid_rewrite IHphi. split; intros H d; eapply sat_ext. 2, 4: apply (H d).
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
        + setoid_rewrite IHphi. split; intros [d H]; exists d; eapply sat_ext. 2, 4: apply H.
          all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
    Qed.

    Lemma sat_subst rho sigma phi :
      (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
    Proof.
      intros H. rewrite sat_comp. apply sat_ext. intros x. now rewrite <- H.
    Qed.

    Lemma sat_single (rho : nat -> D) (Phi : form) (t : term) :
      (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
    Proof.
      rewrite sat_comp. apply sat_ext. now intros [].
    Qed.

    
  End Substs.


  
  
  Section Vector.

    Variable D : Type.
    Variable I : interp D.


    Notation "v '∗' rho" := (join v rho) (at level 20).

    
    Lemma le_ex x y :
      x <= y <-> exists k, x + k = y.
    Proof.
      split.
      - intros. exists (y - x). lia.
      - intros [k <-]. lia.
    Qed.

      
    Lemma split_merge_eq phi N sigma :
      (first_of N sigma ∗ rest_of N sigma) ⊨ phi <-> sigma ⊨ phi. 
    Proof.
      apply sat_ext. intros x.
      destruct (Compare_dec.le_lt_dec (S N) x) as [H | H].
      - rewrite le_ex in H. destruct H as [k <-].
        rewrite (vec_join_after_N (first_of N sigma) (rest_of N sigma) ).
        unfold rest_of. f_equal. lia.
      - apply vec_join_before_N'. lia.
    Qed.
    
              

    Lemma vec_exists n phi rho :
      rho ⊨ (exist_times n phi) <-> exists v : vec D n, v ∗ rho ⊨ phi.
    Proof.
      split; revert rho; induction n; cbn.
      - cbn. exists (Vector.nil D); tauto.
      - intros rho [d H]. destruct (IHn _ H) as [v IH].
        exists (Vector.cons D d _ v). now cbn.
      - intros rho [v H]. revert H. now rewrite (vec_Onil_eq v). 
      - intros rho [v H]. exists (Vector.hd v). apply IHn. exists (tl v).
        change (Vector.cons _ (Vector.hd v) _ (tl v) ∗ rho ⊨ phi ).
        now rewrite <- vec_hdtl_eq.
    Qed.

        
    Lemma max_term_ext N t rho sigma :
      max_term t <= N -> (forall n, n <= N -> rho n = sigma n) -> eval rho t = eval sigma t.
    Proof.
      induction t.
      - cbn. intros HN Hext. now apply Hext.
      - intros HN Hext. cbn. f_equal.
        apply map_ext_in. intros. apply IH; try assumption.
        now apply (max_term_parts HN), vec_map_In.
    Qed.

    

    Lemma vec_join_shiftin N phi (v : vec D (S N)) (rho sigma : nat -> D) (x : D) :
      (x .: v ∗ rho) ⊨ phi -> (join (Vector.shiftin x v) rho ⊨ phi <-> join (Vector.shiftin x v) sigma ⊨ phi) -> (x .: v ∗ sigma) ⊨ phi.
    Proof.
      intros H' H.
      eapply sat_ext. 2: rewrite <- H.
      intros y. induction v in sigma |- *; cbn; trivial.
      eapply sat_ext. 2: apply H'.
      intros y. induction v in rho |- *; cbn; trivial.
    Qed.

    
    Lemma vec_change N phi (v : vec D (S N) ) rho sigma :
      max_form phi <= N -> v∗rho ⊨ phi <-> v∗sigma ⊨ phi.
    Proof.
      induction phi in N, v |- *.
      - tauto.
      - cbn. intros HN.
        enough ( Vector.map (eval (v ∗ rho)) v0 = Vector.map (eval (v ∗ sigma)) v0) as Eq.
        now rewrite Eq. apply map_ext_in. intros x Hx.
        refine (@max_term_ext _ _ _ _ _ _ ).
        refine (vec_max_entries _ _ HN _ _).
        now apply vec_map_In. apply vec_join_ext.
      - destruct b; cbn; specialize (IHphi1 N v); specialize (IHphi2 N v);
          intros [H1 H2] % PeanoNat.Nat.max_lub_iff; firstorder.
      - destruct q.
        + intros HN. split.
          intros H x. cbn in H. specialize (H x).
          apply vec_join_shiftin with rho; trivial. apply IHphi. firstorder.
          intros H x. cbn in H. specialize (H x).
          apply vec_join_shiftin with sigma; trivial. rewrite IHphi; firstorder.
        + intros HN. split.
          cbn. intros [x H]. exists x.
          apply vec_join_shiftin with rho; trivial. apply IHphi. firstorder.
          cbn. intros [x H]. exists x.
          apply vec_join_shiftin with sigma; trivial. rewrite IHphi; firstorder.
    Qed.
    

    
        
  End Vector.

      
  Section Top.

    Variable D : Type.
    Variable I : interp D.

    Definition U phi := fun x => forall rho, (x.:rho) ⊨ phi.

    Definition inters {J} (Phi : J -> form) := fun x => forall rho i, (x.:rho) ⊨ Phi i.
    Definition union {J} (Phi : J -> form) := fun x => forall rho, exists i, (x.:rho) ⊨ Phi i.
    Definition com phi := fun x => ~ U phi x.

    
    Goal D -> forall phi x, U (phi --> ⊥) x -> com phi x.
    Proof.
      intros d phi x. unfold com. unfold U; cbn. intros H1 H2.
      apply (H1 (fun _ => d) ). apply H2.
    Qed.

    


  End Top.
        



  
End Tarski.

Arguments sat {_ _ _} _ _, _ _ _ _ _.
Notation "rho ⊨ phi" := (sat _ rho phi) (at level 20).


