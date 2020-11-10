Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import PA.
Require Import List.
Require Import Lia.
Require Import List.
Require Import Equations.Equations Equations.Prop.DepElim.
Import ListNotations.



(* Wrapper around prv to use custom notation only in the goal *)
Inductive pm {p cf cp} A phi := PM : @prv p cf cp A phi -> pm A phi.
Definition pm2prv {p cf cp} A phi : pm A phi -> @prv p cf cp A phi := fun p => match p with PM _ _ x => x end.
Definition prv2pm {p cf cp} A phi : @prv p cf cp A phi -> pm A phi := fun x => PM A phi x.

(* The context notation gets a new scope that is only applied in pm terms. *)
(* Otherwise all lists would be printed that way.  *)
Declare Scope context_scope.
Arguments pm _ _ _ _%context_scope.
Arguments cons _ _ _%context_scope.

Notation "" := nil (only printing) : context_scope.
Notation "H A" := (cons H A)
  (at level 1, A at level 200, H at level 200,
  left associativity, format "'[' H ']' '//' A", only printing) : context_scope.

Notation " A '⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯' phi" :=
  (pm A phi)
  (at level 1, left associativity,
  format "A '//' '⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯' '//' phi", only printing).

(* Tactics to toggle notation in the goal *)
Ltac fstart := apply pm2prv.
Ltac fstop := apply prv2pm.

(* All the tactics defined below work with the original "prv" type. *)
(* The following tactic lifts them to be compatible with "pm". *)
Ltac make_compatible tac :=
  match goal with
  | [ |- pm _ _ ] => fstop; tac; fstart
  | _ => tac
  end.


(** Basic tactics *)

(* Ltac ctx' := tryif (left; reflexivity) then idtac else (right; ctx').
Ltac ctx := apply Ctx; ctx'. *)
Ltac ctx := make_compatible ltac:(apply Ctx; firstorder).

Ltac fexfalso := make_compatible ltac:(apply Exp).
Ltac fsplit := make_compatible ltac:(apply CI).
Ltac fleft := make_compatible ltac:(apply DI1).
Ltac fright := make_compatible ltac:(apply DI2).

Ltac fintro := make_compatible ltac:(
  match goal with 
  | [ |- ?A ⊢ ∀ ?t ] => apply AllI
  | [ |- ?A ⊢ (?s --> ?t) ] => apply II
  end).
Ltac fintros := make_compatible ltac:(repeat fintro).


(* Lemma fintro_help A s t :
  ((s::A) ⊢ s -> (s::A) ⊢ t) -> A ⊢ (s --> t).
Proof.
  intros. apply II. assert ((s::A) ⊢ s). ctx.
  eapply Weak. apply H. assumption. firstorder.
Qed.

Ltac fintro H := 
  match goal with 
  | [ |- ?A ⊢ ∀ ?t ] => apply AllI
  | [ |- ?A ⊢ (?s --> ?t) ] => apply fintro_help; intros H
  end.

Ltac fintros := repeat (let H := fresh "H" in fintro H). *)


(** [ctx2hyp n as H]

  Lifts the n'th assumption in the ND context to a Coq hypothesis.
*)
Ltac ctx2hyp'' n H A := 
  match n with
  | 0 => match A with ?t::_ => assert ([t] ⊢ t) as H by ctx end
  | S ?n' => match A with _::?A' => ctx2hyp'' n' H A' end
  end.

Ltac ctx2hyp' n H :=
  match goal with [ |- ?A ⊢ _ ] => ctx2hyp'' n H A end.

Tactic Notation "ctx2hyp" integer(n) "as" reference(H) := make_compatible ltac:(ctx2hyp' n H).



(** [fspecialize (H x1 x2 ... xn)] or [fspecialize H with x1 x2 ... xn] 
  
  Specializes a hypothesis H of the form [X ⊢ ∀∀...∀ p1 --> ... --> pn --> g] 
  with x1, x2, ..., xn.
*)

(* Spimplify terms that occur during specialization  *)
Ltac simpl_subst H :=
  cbn in H;
  repeat match type of H with
  | context C[subst_term ?s ?t] => let H' := context C[t[s]] in change H' in H
  end;
  repeat match type of H with
  | context C[?t[S >> var]] => let H' := context C[t[↑]] in change H' in H
  end;
  try rewrite !up_term in H;
  try rewrite !subst_term_shift in H.

Ltac fspecialize_list H A := 
  match A with
  | [] => simpl_subst H
  | ?x::?A' => 
      tryif 
        apply (fun H => IE _ _ _ H x) in H
      then idtac
      else (
        (* For some reason we cannot directly [apply (AllE _ x)]
           if x contains ⊕, σ, etc. But evar seems to work. *)
        let x' := fresh "x" in 
        eapply (AllE _ ?[x']) in H; 
        instantiate (x' := x) );
    fspecialize_list H A'
  end.

Tactic Notation "fspecialize" "(" hyp(H) constr(x1) ")" := make_compatible ltac:(fspecialize_list H constr:([x1])).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) ")" := make_compatible ltac:(fspecialize_list H constr:([x1; x2])).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fspecialize_list H constr:([x1;x2;x3])).

Tactic Notation "fspecialize" hyp(H) "with" constr(x1) := make_compatible ltac:(fspecialize_list H constr:([x1])).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) := make_compatible ltac:(fspecialize_list H constr:([x1;x2])).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) constr(x3) := make_compatible ltac:(fspecialize_list H constr:([x1;x2;x3])).




(** [fapply (H x1 ... xn)], [feapply (H x1 ... xn)]
  
  Works on
  - Coq hypothesis by name
  - Formula in in ND context by index or explicit formula: [fapply 3], [fapply ax_symm]
*)

(* Helper tactics: *)

(* [fapply_without_quant] takes a formula [H : X ⊢ p1 --> p2 --> ... --> pn --> g] 
  without leading quantifiers. It solves the goal [X ⊢ g] by adding subgoals for
  each premise p1, p2, ..., pn. *)
Ltac fapply_without_quant H :=
  tryif exact H then idtac else
  match type of H with
  | ?A ⊢ (?s --> ?t) => 
    let Hs := fresh "Hs" in 
    let Ht := fresh "Ht" in 
    enough (A ⊢ s) as Hs; 
    [ assert (A ⊢ t) as Ht; 
      [ apply (IE _ _ _ H Hs) | fapply_without_quant Ht; clear Hs; clear Ht ] 
    | ]
  end.

Ltac instantiate_evars H := repeat eapply AllE in H.
Tactic Notation "is_hyp" hyp(H) := idtac.
Ltac nth A n :=
  match n with
  | 0 => match A with ?t :: _ => t end
  | S ?n' => match A with _ :: ?A' => nth A' n' end
  end.

(* Check wether T is a hypothesis, a context index or a context formula
  and put it into hypothesis H. *)
Ltac turn_into_hypothesis T H :=
  tryif is_hyp T
  then assert (H := T)  (* Hypothesis *)
  else match goal with [ |- ?C ⊢ _ ] => 
    match type of T with
    | form => assert (C ⊢ T) as H by ctx  (* Explicit form *)
    | nat => let T' := nth C T in assert (C ⊢ T') as H by ctx  (* Idx in context *)
    end
  end.

Ltac feapply' T A := 
  let H := fresh "H" in
  turn_into_hypothesis T H;
  fspecialize_list H A;
  instantiate_evars H;
  simpl_subst H;
  match goal with [ |- ?C ⊢ _ ] => 
    eapply (Weak _ C) in H; [| firstorder]
  end;
  fapply_without_quant H;
  clear H.

Ltac fapply' T A := 
  let H := fresh "H" in
  turn_into_hypothesis T H;
  fspecialize_list H A; 
  instantiate_evars H; 
  simpl_subst H;
  match goal with [ |- ?U ⊢ _ ] => 
    eapply (Weak _ U) in H; [| firstorder]
  end;
  fapply_without_quant H;
  (* Evars should only be used for unification in [fapply]. *)
  (* Therefore reject, if there are still evars visible. *)
  (* TODO: This is not optimal. If the goal contains evars, 
     H might still contain evars after unification and we would fail. *)
  tryif has_evar ltac:(type of H) 
  then fail "Cannot find instance for variable. Try feapply?" 
  else clear H.


Tactic Notation "feapply" constr(T) := make_compatible ltac:(feapply' T constr:([] : list form)).
Tactic Notation "feapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(feapply' T constr:([x1])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(feapply' T constr:([x1;x2])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(feapply' T constr:([x1;x2;x3])).

Tactic Notation "fapply" constr(T) := make_compatible ltac:(fapply' T constr:([] : list form)).
Tactic Notation "fapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(fapply' T constr:([x1])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(fapply' T constr:([x1;x2])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fapply' T constr:([x1;x2;x3])).






Section FullLogic.

  Variable p : peirce.


  (* Basic tactics *)
  Ltac freflexivity := fapply ax_refl.



  (** [fdestruct n]

    Destructs the n'th assumption in the ND context back into
    the ND context.
  *)

  Lemma fdestruct_and A s t G :
    (s::t::A) ⊢ G -> (s ∧ t::A) ⊢ G.
  Proof.
    intros. apply switch_imp. apply switch_conj_imp. 
    repeat apply <- switch_imp. fapply H.
  Qed.

  Lemma fdestruct_or A s t G :
    (s::A) ⊢ G -> (t::A) ⊢ G -> (s ∨ t::A) ⊢ G.
  Proof.
    intros Hs Ht. eapply DE. ctx. fapply Hs. fapply Ht.
  Qed.

  Ltac fdestruct n := make_compatible ltac:(
  match n with
  | 0 => 
    match goal with 
    | [ |- (?s ∧ ?t :: ?A) ⊢ ?G ] => apply fdestruct_and 
    | [ |- (?s ∨ ?t :: ?A) ⊢ ?G ] => apply fdestruct_or
    end
  | S ?n' => idtac "TODO"
  end).








  (* ---------------------------------------------------------------------------- *)
  (*                                    DEMO                                      *)
  (* ---------------------------------------------------------------------------- *)

  Definition FA' := ax_add_zero::ax_add_rec::ax_mult_zero::ax_mult_rec::nil.

  Definition ax_refl := (∀ $0 == $0).
  Definition ax_sym := (∀ ∀ $0 == $1 --> $1 == $0).
  Definition ax_trans := (∀∀∀ $0 == $1 --> $1 == $2 --> $0 == $2).

  Definition ax_eq_succ := (∀∀ $0 == $1 --> σ $0 == σ $1).
  Definition ax_eq_add := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3).
  Definition ax_eq_mult := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3).

  Definition FA := ax_refl::ax_sym::ax_trans::ax_eq_succ::ax_eq_add::ax_eq_mult::FA'.

  Lemma num_add_homomorphism x y :
    FA ⊢ (num x ⊕ num y == num (x + y)).
  Proof.
    induction x; cbn.
    - fapply ax_add_zero.  (* Arguments are infered! *)
    - feapply ax_trans.
      + feapply ax_eq_succ. exact IHx.
      + fapply ax_add_rec.
  Qed.

  Lemma num_mult_homomorphism x y : FA ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
    induction x; cbn.
    - fapply ax_mult_zero.
    - feapply ax_trans.
      + apply num_add_homomorphism.
      + feapply ax_trans.
        * feapply ax_eq_add. exact IHx. fapply ax_refl.
        * fapply ax_mult_rec.
  Qed.



  Lemma leibniz_term (t t' s : term) :
    FA ⊢ (t == t' --> s[t..] == s[t'..]).
  Proof.
    fintros. induction s; cbn.
    - destruct x; cbn. ctx. freflexivity.
    - destruct F; repeat depelim v; cbn.
      * freflexivity.
      * fapply ax_eq_succ. apply IH. left.
      * fapply ax_eq_add; apply IH. right. left. left.
      * fapply ax_eq_mult; apply IH. right. left. left.
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
      pose (leibniz_term t t' h0) as H'. fapply H'. fapply H.
      feapply ax_trans. ctx.
      pose (leibniz_term t' t h) as H'. fapply H'. fapply ax_sym. fapply H.
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
        (* enough (forall u1 u2, FA ⊢ ((∀ phi[u1][up t..][u2]) --> (∀ phi[u1][up t'..][u2]))).
        { specialize (H0 var var). now rewrite !subst_var in H0. }
        assert (forall (t t' : term) u1 u2, FA ⊢ (t == t') -> FA ⊢ (phi[u1][t..][u2] --> phi[u1][t'..][u2])) as IH' by admit. *)

        intros. fintros. 
        change (((∀ phi)[t..][↑] :: map (subst_form ↑) A) ⊢ phi[up t'..]).
        change ((∀ phi[up t..][up ↑] :: map (subst_form ↑) A) ⊢ phi[up t'..]).
        (* ? *)
  Admitted.






  (* Returns a new formula where all occurences of "t" are turned into *)
  (* "($0)[t..]" and every other term "s" into "s[↑][t..]". *)
  Ltac add_shifts G t := (* TODO: Quantors :( *)
    let f := add_shifts in 
    match G with
    | t => constr:(($0)[t..])
    | $(?n) => constr:(($n)[↑][t..])
    | ?u --> ?v => let u' := f u t in let v' := f v t in constr:(u' --> v')
    | ?u ∧ ?v => let u' := f u t in let v' := f v t in constr:(u' ∧ v')
    | ?u ∨ ?v => let u' := f u t in let v' := f v t in constr:(u' ∨ v')
    | ?u ⊕ ?v => let u' := f u t in let v' := f v t in constr:(u' ⊕ v')
    | ?u ⊗ ?v => let u' := f u t in let v' := f v t in constr:(u' ⊗ v')
    | ?u == ?v => let u' := f u t in let v' := f v t in constr:(u' == v')
    | σ ?u => let u' := f u t in  constr:(σ u')
    | ?u => constr:(u[↑][t..]) 
            (* TODO: Why doesn't this work: *) (* tryif is_var u then constr:(u[↑][t..]) else fail *)
    end.

  (* Returns a new formula where all occurences of "s[↑][t..]" in G are  *)
  (* turned into "s[↑]" and "($0)[t]" into "$0". *)
  Ltac remove_shifts G t :=
    match G with 
    | context C[ ?s[↑][t..] ] => let G' := context C[ s[↑] ] in remove_shifts G' t
    | context C[ ($0)[t..] ] => let G' := context C[ $0 ] in remove_shifts G' t
    | _ => G
    end.

  Ltac frewrite' T A back :=
    let H := fresh "H" in
    turn_into_hypothesis T H;
    fspecialize_list H A; 
    instantiate_evars H; 
    simpl_subst H;
    match type of H with _ ⊢ (?_t == ?_t') =>
      let t := match back with true => _t' | false => _t end in
      let t' := match back with true => _t | false => _t' end in

      (* 1. Replace each occurence of "t" with "($0)[t..]" and every other *)
      (*  "s" with "s[↑][t..]". The new formula is created with the [add_shifts] *)
      (*  tactic and proven with the shift lemmas. *)
      match goal with [ |- ?C ⊢ ?G ] => 
        let X := fresh in 
        let G' := add_shifts G t in
        enough (C ⊢ G') as X;
        [ try rewrite !subst_shift in X; try rewrite !subst_term_shift in X; apply X |]
      end;

      (* 2. Pull out the [t..] substitution *)
      match goal with [ |- ?U ⊢ ?G ] =>
        let G' := remove_shifts G t in change (U ⊢ G'[t..])
      end;

      (* 3. Change [t..] to [t'...] using leibniz. For some reason  *)
      (*  we cannot directly [apply leibniz with (t := t')] if t'  *)
      (*  contains ⊕, σ, etc. But evar seems to work. *)
      let t'' := fresh "t" in 
      eapply (leibniz _ _ ?[t'']);
      [ instantiate (t'' := t'); firstorder |
        match back with
        | false => feapply ax_sym; apply H
        | true => apply H
        end
      | ];

      (* 4. Pull substitutions inward *)
      cbn;

      (* 5. Turn subst_term calls back into []-Notation *)
      repeat match goal with [ |- context C[subst_term t'.. ?s[↑]] ] =>
        let G' := context C[ s[↑][t'..] ] in change G'
      end;

      (* 6. Simplify *)
      try rewrite !subst_shift;
      try rewrite !subst_term_shift;
      repeat match goal with [ |- context C[func Zero (Vector.nil term)] ] =>
        let G' := context C[zero] in change G'
      end
    end;
    clear H.
  
  Tactic Notation "frewrite" constr(T) := frewrite' T constr:([] : list form) constr:(false).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) ")" := frewrite' T constr:([x1]) constr:(false).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) ")" := frewrite' T constr:([x1;x2]) constr:(false).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := frewrite' T constr:([x1;x2;x3]) constr:(false).
  
  Tactic Notation "frewrite" "<-" constr(T) := frewrite' T constr:([] : list form) constr:(true).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) ")" := frewrite' T constr:([x1]) constr:(true).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) ")" := frewrite' T constr:([x1;x2]) constr:(true).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := frewrite' T constr:([x1;x2;x3]) constr:(true).








  (* With [frewrite] the proofs from above get even shorter! *)

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


  (* Rewrite directly from the context: *)
  Goal forall t t', FA ⊢ (t == t' --> zero ⊕ σ t == σ t').
  Proof.
    intros. fintros. frewrite 0. fapply ax_add_zero.
  Qed.


  (* Nice context notation using [fstart] *)
  Goal forall a b c, FA ⊢ (a --> (a --> b) --> (b --> c) --> c).
  Proof.
    intros. fstart. fintros. fapply 0. fapply 1. ctx.
  Qed.


