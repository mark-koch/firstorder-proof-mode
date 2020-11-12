Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import PA.
Require Import List.
Require Import Lia.
Require Import List.
Require Import String.
Require Import Equations.Equations Equations.Prop.DepElim.
Import ListNotations.

Open Scope string_scope.

(* 
  I want to have an Iris-like proof mode, where the context is displayed
  above a line with the current goal below. Also the assumptions should
  have names.

  This is not possible using the `prv` type. Thus the plan is to embedd
  deductions into another type `pm` that contains additional information.

  Note that this mode is strictly optional! All of the apply, rewrite, etc.
  tactics defined below work on the `prv` type and are lifted to `pm` on
  demand.
*)


(* Extended formula list with names *)
Inductive context := 
  | cnil 
  | ccons : string -> form -> context -> context
  | cblackbox : list form -> context.  (* For unknown lists, we don't want to look into *)


(** Context utilities *)

Definition digit_to_string n := match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5" 
  | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9" | _ => "_"
end.
Fixpoint nat_to_string' fuel n := match fuel with
  | 0 => "OUT OF FUEL"
  | S fuel' => match n with
    | 0 => ""
    | _ =>  nat_to_string' fuel' (Nat.div n 10)  ++ digit_to_string (Nat.modulo n 10)
    end
end.
Definition nat_to_string n := match n with 0 => "0" | _ => nat_to_string' 100 n end.

(* Returns the index of the first occurence of `name` in the 
 * context `C`, or `None` if it doesn't exist. *)
Fixpoint lookup' n C name :=
  match C with
  | ccons s _ C' => if string_dec s name then Some n else lookup' (S n) C' name
  | _ => None
  end.
Definition lookup := lookup' 0.

(* Finds the first name of form `H`, `H0`, `H1`, ... thats not 
 * contained in the context `C`. *)
Fixpoint new_name' n C fuel := match fuel with
  | 0 => "OUT OF FUEL"
  | S fuel' =>
    let name := match n with 0 => "H" | S n' => "H" ++ nat_to_string n' end in
    match lookup C name with
    | None => name
    | Some _ => new_name' (S n) C fuel'
    end
end.
Definition new_name C := new_name' 0 C 100.

(* For context creation we need to give names to the initial formulas.
 * This is done using syntactic matching with ltac instead of a Galina
 * function, because if we want to prove `A ⊢ φ` for an unknown A we 
 * don't want to go into the `A`. *)
Ltac create_context' A :=
  match A with
  | ?phi::?A' =>
    let x := create_context' A' in match x with (?c, ?n) =>
      match n with
        | 0 => constr:((ccons "H" phi c, S n))
        | S ?n' => let s' := eval cbn in ("H" ++ nat_to_string n') in constr:((ccons s' phi c, S n))
      end
    end
  | nil => constr:((cnil, 0))
  | _ => 
    (* If it's not a cons or nil, it's a variable/function call/... 
     * and we don't want to look into it *)
    constr:((cblackbox A, 0))
  end.
Ltac create_context A := let x := create_context' A in match x with (?c, _) => c end.



(* `pm` embedds a `prv` derivation together with a context *)
Inductive pm {p cf cp} (C: context) A phi := PM : @prv p cf cp A phi -> pm C A phi.

Definition pm2prv {p cf cp} C A phi : pm C A phi -> @prv p cf cp A phi := fun p => match p with PM _ _ _ x => x end.
Definition prv2pm {p cf cp} C A phi : @prv p cf cp A phi -> pm C A phi := fun x => PM C A phi x.

(* Declare Scope context_scope.
Delimit Scope context_scope with env.
Notation "" := EmptyString (only printing) : context_scope.
Notation "c ,, S" := (String c S) (at level 200, left associativity, only printing, format "c ,, S") : context_scope.
Arguments ccons _%context_scope _ _.
Open Scope context_scope. *)

Notation "" := cnil (only printing).
Notation "A" := (cblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (ccons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Arguments pm {_} {_} {_} _ {_} _.
Notation " C '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm C phi)
  (at level 1, left associativity,
  format "C '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).


(* Tactics to toggle proof mode *)
Ltac fstart := match goal with [ |- ?A ⊢ _ ] => let C := create_context A in apply (pm2prv C) end.
Ltac fstop := apply prv2pm.


(* All the tactics defined below work with the original `prv` type.
 * The following tactic lifts them to be compatible with `pm`.
 *
 * Every tactic must have an additional argument where the current
 * context is filled in if the proof mode is active, and `cnil` 
 * otherwise. *)
Ltac make_compatible tac :=
  match goal with
  | [ |- pm ?C _ ] => apply prv2pm; tac C; apply (pm2prv C)
  | _ => tac cnil
  end.



(** Basic tactics *)

Ltac ctx := make_compatible ltac:(fun _ => apply Ctx; firstorder).

Ltac fexfalso := make_compatible ltac:(fun _ => apply Exp).
Ltac fsplit := make_compatible ltac:(fun _ => apply CI).
Ltac fleft := make_compatible ltac:(fun _ => apply DI1).
Ltac fright := make_compatible ltac:(fun _ => apply DI2).


(* 
 * [fintro], [fintros] 
 * 
 * Similar to Coq. Identifiers need to be given as strings (e.g. 
 * [fintros "H1" "H2"]). With "?" you can automatically generate
 * a name (e.g. [fintros "?" "H"])  
 *)
Ltac fintro' id :=
  match goal with 
  | [ |- ?A ⊢ ∀ ?t ] => apply AllI
  | [ |- ?A ⊢ (?s --> ?t) ] => apply II
  (* Special care for intro in proof mode *)
  | [ |- pm ?C (∀ ?t) ] => make_compatible ltac:(apply AllI)
  | [ |- pm ?C (?s --> ?t) ] =>
      apply prv2pm; 
      apply II;
      let name := 
        match id with 
        | "?" => eval cbn in (new_name C)
        | _ => match eval cbn in (lookup C id) with
          | None => id
          | Some _ => let msg := eval cbn in ("Identifier already used: " ++ id) in fail 2 msg
          end
        end
      in apply (pm2prv (ccons name s C))
  end.
Tactic Notation "fintro" := fintro' constr:("?").
Tactic Notation "fintro" constr(H) := fintro' H.
Tactic Notation "fintros" := repeat fintro.

Ltac fintros' ids := 
  match ids with
  | [] => idtac 
  | ?id::?ids' => fintro id; fintros' ids'
  end.
Tactic Notation "fintros" constr(H1) := fintros' constr:([H1]).
Tactic Notation "fintros" constr(H1) constr(H2) := fintros' constr:([H1;H2]).
Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) := fintros' constr:([H1;H2;H3]).
Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) constr(H4) := fintros' constr:([H1;H2;H3;H4]).



(* 
 * [ctx2hyp n as H]
 *
 * Lifts the n'th assumption in the ND context to a Coq hypothesis.
 *)
Ltac ctx2hyp'' n H A := fun _ => 
  match n with
  | 0 => match A with ?t::_ => assert ([t] ⊢ t) as H by ctx end
  | S ?n' => match A with _::?A' => ctx2hyp'' n' H A' end
  end.

Ltac ctx2hyp' n H := fun _ => 
  match goal with [ |- ?A ⊢ _ ] => ctx2hyp'' n H A end.

Tactic Notation "ctx2hyp" integer(n) "as" reference(H) := make_compatible ltac:(ctx2hyp' n H).



(* 
 * [fspecialize (H x1 x2 ... xn)], [fspecialize H with x1 x2 ... xn] 
 * 
 * Specializes a Coq hypothesis `H` of the form `X ⊢ ∀∀...∀ p1 --> ... --> pn --> g`
 * with `x1, x2, ..., xn`.
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

Tactic Notation "fspecialize" "(" hyp(H) constr(x1) ")" := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1])).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) ")" := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1; x2])).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1;x2;x3])).

Tactic Notation "fspecialize" hyp(H) "with" constr(x1) := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1])).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1;x2])).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) constr(x3) := make_compatible ltac:(fun _ => fspecialize_list H constr:([x1;x2;x3])).




(*
 * [fapply (H x1 ... xn)], [feapply (H x1 ... xn)]
 *  
 * Works on
 * - Coq hypothesis by name
 * - Formula in in ND context by index (e.g. [fapply 3])
 * - Explicit formula type in the context (e.g. [fapply ax_symm])
 * - Name of a context assumption in proof mode (e.g. [fapply "H2"])
 *)

(* Helper tactics: *)

(* [fapply_without_quant] takes a formula `H : X ⊢ p1 --> p2 --> ... --> pn --> g`
 * without leading quantifiers. It solves the goal `X ⊢ g` by adding subgoals for
 * each premise `p1, p2, ..., pn`. *)
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

(* Check wether T is a hypothesis, a context index, a context formula
 * or a context name and put it into hypothesis H. *)
Ltac turn_into_hypothesis T H context := 
  tryif is_hyp T
  then assert (H := T)  (* Hypothesis *)
  else match goal with [ |- ?C ⊢ _ ] => 
    match type of T with
    | form => assert (C ⊢ T) as H by ctx  (* Explicit form *)
    | nat => let T' := nth C T in assert (C ⊢ T') as H by ctx  (* Idx in context *)
    | string => match eval cbn in (lookup context T) with  (* Context name *)
      | None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
      | Some ?n => let T' := nth C n in assert (C ⊢ T') as H by ctx
      end
    end
  end.

Ltac feapply' T A := fun contxt =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  fspecialize_list H A;
  instantiate_evars H;
  simpl_subst H;
  match goal with [ |- ?C ⊢ _ ] => 
    eapply (Weak _ C) in H; [| firstorder]
  end;
  fapply_without_quant H;
  clear H.

Ltac fapply' T A contxt :=
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  fspecialize_list H A; 
  instantiate_evars H; 
  simpl_subst H;
  match goal with [ |- ?U ⊢ _ ] => 
    eapply (Weak _ U) in H; [| firstorder]
  end;
  fapply_without_quant H;
  (* Evars should only be used for unification in [fapply].
   * Therefore reject, if there are still evars visible. *)
  (* TODO: This is not optimal. If the goal contains evars, 
   * H might still contain evars after unification and we would fail. *)
  tryif has_evar ltac:(type of H) 
  then fail 2 "Cannot find instance for variable. Try feapply?" 
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

  Goal forall a b c, [a;b;c] ⊢ (b-->c-->c).
  Proof.
    intros. fstart. fintros. fapply "H".
  Qed.

  (*
   * [fdestruct n]
   *
   *  Destructs the n'th assumption in the ND context back into
   * the ND context.
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

  Ltac fdestruct n := make_compatible ltac:( fun _ =>
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






  (* Returns a new formula where all occurences of `t` are turned into
   * `($0)[t..]` and every other term `s` into `s[↑][t..]`. *)
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

  (* Returns a new formula where all occurences of `s[↑][t..]` in G are
   * turned into `s[↑]` and `($0)[t]` into `$0`. *)
  Ltac remove_shifts G t :=
    match G with 
    | context C[ ?s[↑][t..] ] => let G' := context C[ s[↑] ] in remove_shifts G' t
    | context C[ ($0)[t..] ] => let G' := context C[ $0 ] in remove_shifts G' t
    | _ => G
    end.

  Ltac frewrite' T A back := fun contxt =>
    let H := fresh "H" in
    turn_into_hypothesis T H contxt;
    fspecialize_list H A; 
    instantiate_evars H; 
    simpl_subst H;
    match type of H with _ ⊢ (?_t == ?_t') =>
      let t := match back with true => _t' | false => _t end in
      let t' := match back with true => _t | false => _t' end in

      (* 1. Replace each occurence of `t` with `($0)[t..]` and every other
       *  "s" with "s[↑][t..]". The new formula is created with the [add_shifts]
       *  tactic and proven with the shift lemmas. *)
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

      (* 3. Change [t..] to [t'...] using leibniz. For some reason
       *  we cannot directly [apply leibniz with (t := t')] if t'
       *  contains ⊕, σ, etc. But evar seems to work. *)
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
  
  Tactic Notation "frewrite" constr(T) := make_compatible ltac:(frewrite' T constr:([] : list form) constr:(false)).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) ")" := make_compatible ltac:(frewrite' T constr:([x1]) constr:(false)).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2]) constr:(false)).
  Tactic Notation "frewrite" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2;x3]) constr:(false)).
  
  Tactic Notation "frewrite" "<-" constr(T) := make_compatible ltac:(frewrite' T constr:([] : list form) constr:(true)).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) ")" := make_compatible ltac:(frewrite' T constr:([x1]) constr:(true)).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2]) constr:(true)).
  Tactic Notation "frewrite" "<-" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(frewrite' T constr:([x1;x2;x3]) constr:(true)).








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



  (* Proof mode demo: *)

  Goal forall t t', FA ⊢ (t == t' --> zero ⊕ σ t == σ t').
  Proof.
    intros. fstart. fintros. frewrite "H". fapply ax_add_zero.
  Qed.

  Goal forall a b c, [] ⊢ (a --> (a --> b) --> (b --> c) --> c).
  Proof.
    intros. fstart. fintros. fapply "H1". fapply "H0". fapply "H".
  Qed.


  (* Rewrite under ∀ test: *)

  Lemma subst_term_up_shift (s : term) t :
    s[up ↑][up t..] = s.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. intros. destruct n; cbn; reflexivity.
  Qed.

  Goal forall t t', FA ⊢ (t == t') -> FA ⊢ ∀ $0 ⊕ σ t[↑] == t' ⊕ σ $0.
  Proof.
    intros.
    enough (FA ⊢ ∀ ($0)[up ↑][up t..] ⊕ σ ($0)[↑][up t..] == t'[up ↑][up t..] ⊕ σ ($0)[up ↑][up t..]) as X
    by now rewrite !subst_term_up_shift in X; rewrite up_term in X.
    change (FA ⊢ (∀ ($0)[up ↑] ⊕ σ ($0)[↑] == t'[up ↑] ⊕ σ ($0)[up ↑])[t..]).
    
    apply leibniz with (t := t'). firstorder. now fapply ax_sym.

    cbn.
    change (FA ⊢ ∀ $0 ⊕ σ t'[↑] == t'[up ↑][up t'..] ⊕ σ $0).
    enough (FA ⊢ ∀ $0 ⊕ σ t'[↑] == t' ⊕ σ $0) by now rewrite subst_term_up_shift.
  Abort.
    
