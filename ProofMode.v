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
 * I want to have an Iris-like proof mode, where the context is displayed
 * above a line with the current goal below. Also the assumptions should
 * have names.
 * This is all done using notation. But this notation should only be applied
 * in the goal, not in other hypothesis. Therefore I define aliases for 
 * `prv` and lists that the notation can match for. Also the list alias
 * holds the assumption names as an extra argument.
 *)


Definition variable_names := list string.
Definition vnil : variable_names := @nil string.
Definition vcons (s : string) (V : variable_names) : variable_names := @cons string s V.

Definition pm {p cf cp} (V : variable_names) C phi := @prv p cf cp C phi.
Arguments pm {_} {_} {_} _ _.

Definition cnil := @nil form.
Definition ccons (s : string) phi C := @cons form phi C.

(* Special alias for unknown lists. Only used to indent with one space in Notation *)
Definition cblackbox (A : list form) := A.  


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
Ltac lookup' n C name :=
  match C with
  | ccons name _ _ => constr:(Some n) 
  | ccons _ _ ?C' => lookup' (S n) C' name
  | vcons name _ => constr:(Some n) 
  | vcons _ ?V' => lookup' (S n) V' name
  | _ => None
  end.
Ltac lookup := lookup' 0.

Ltac nth A n :=
  match n with
  | 0 => match A with ?t :: _ => t | ccons _ ?t _ => t | vcons ?t _ => t end
  | S ?n' => match A with _ :: ?A' => nth A' n' | ccons _ _ ?A' => nth A' n' | vcons _ ?A' => nth A' n' end
  end.

Ltac map_ltac A f :=
  match A with
  | nil => nil
  | cnil => cnil
  | vnil => vnil
  | @Vector.nil ?a => constr:(@Vector.nil a)
  | cblackbox ?A => constr:(cblackbox A)
  | cons ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(cons x' A'')
  | ccons ?s ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(ccons s x' A'')
  | vcons ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(vcons x' A'')
  | Vector.cons ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(Vector.cons x' A'')
  end.

(* Finds the first name of form `base`, `base0`, `base1`, ... thats not 
 * contained in the context/variable list `C`. *)
Ltac new_name' n base C :=
  let name := match n with 
    | 0 => base
    | S ?n' => let s := eval cbn in (nat_to_string n') in eval cbn in (base ++ s)
  end in
  match lookup C name with
  | @None => name
  | @Some _ _ => new_name' (S n) base C
  end.
Ltac new_name base C := new_name' 0 base C.

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
  | ?A' => 
    (* If it's not a cons or nil, it's a variable/function call/... 
     * and we don't want to look into it *)
    constr:((cblackbox A', 0))
  end.
Ltac create_context A := let x := create_context' A in match x with (?c, _) => c end.



(** Variable names utilities: *)

Definition named_quant {fsig psig ops} op (x : string) phi := @quant fsig psig ops op phi.
Definition named_var {fsig} n (x : string) := @var fsig n.
Arguments named_var {_ _} _.

Ltac annotate_term f t :=
  match t with
  | var ?n =>
      let name := eval cbn in (f n) in
      constr:(@named_var _ n name)
  | func ?fu ?v =>
      let map_fun := annotate_term f in
      let v' := map_ltac v map_fun in
      constr:(func fu v')
  | _ => t
  end.

Ltac annotate_form' f idx phi :=
  match phi with
  | fal => fal
  | atom ?P ?v =>
      let map_fun := annotate_term f in
      let v' := map_ltac v map_fun in
      constr:(atom P v')
  | bin ?op ?psi1 ?psi2 => 
      let psi1' := annotate_form' f idx psi1 in
      let psi2' := annotate_form' f idx psi2 in
      constr:(bin op psi1' psi2')
  | quant ?op ?psi =>
      let name := eval cbn in ("x" ++ nat_to_string idx) in
      let f' := constr:(fun n => match n with 0 => name | S n' => f n' end) in
      let psi' := annotate_form' f' (S idx) psi in
      constr:(named_quant op name psi')
  | _ => phi
  end.

Ltac add_binder_names :=
  match goal with [ |- pm ?V ?C ?phi] =>
    let f := constr:(fun (n : nat) => List.nth n V "ERROR") in
    let annotate_form := annotate_form' f 0 in
    let phi' := annotate_form phi in
    let C' := map_ltac C annotate_form in
    change (pm V C' phi')
  end.
Ltac update_binder_names := unfold named_quant; unfold named_var; add_binder_names.



Notation "" := cnil (only printing).
Notation "A" := (cblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (ccons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Notation "∀ x , phi" := (named_quant All x phi) (at level 50, only printing).
Notation "∃ x , phi" := (named_quant Ex x phi) (at level 50, only printing).
(* Notation "§ x" := (named_var x) (at level 30, only printing, format "§ '/' x"). *)
Notation "x" := (named_var x) (at level 1, only printing).

Notation "" := vnil (only printing).
Notation "V , name" := (vcons name V)
  (at level 1, V at level 200, name at level 200,
  left associativity, format "V ,  name", only printing).
Notation "name" := (vcons name vnil) (at level 1, only printing).

Notation " V ':' 'ℕ' C '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm V C phi)
  (at level 1, left associativity,
  format " V  ':'  'ℕ' '//'  C '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).

Notation "C '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm vnil C phi)
  (at level 1, left associativity,
  format " C '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).

Notation " V ':' 'ℕ' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm V cnil phi)
  (at level 1, left associativity,
  format " V  ':'  'ℕ' '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).

Notation "'━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm vnil cnil phi)
  (at level 1, left associativity,
  format "'//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).


(* Tactics to toggle proof mode *)
Ltac fstart := match goal with [ |- ?A ⊢ ?phi ] => 
  let C := create_context A in
  change (pm vnil C phi);
  add_binder_names
end.
Ltac fstop := match goal with [ |- pm ?V ?C ?phi ] => 
  change (prv C phi); unfold pm in *; unfold cnil; unfold ccons;  
  unfold cblackbox; unfold named_quant; unfold named_var 
end.


(* All the tactics defined below work with the original `prv` type.
 * The following tactic lifts them to be compatible with `pm`.
 *
 * Every tactic must have an additional argument where the current
 * context is filled in if the proof mode is active, and `cnil` 
 * otherwise. *)
Ltac make_compatible tac :=
  match goal with
  | [ |- prv ?A _ ] => tac A vnil
  | [ |- pm ?V ?C _ ] => 
    fstop; 
    tac C V;
    match goal with 
    | [ |- pm _ _ ?G ] => change (pm V C G) 
    | [ |- prv _ ?G ] => change (pm V C G)
    | _ => idtac 
    end;
    try update_binder_names (* [try] because some tactics add normal Coq goals *)
  end.




(* Intro pattern parsing 
 * This gets its own section to avoid importing Ascii globally. *)
Section IntroPattern.
  Import Ascii.

  Inductive intro_pattern :=
    | patId : string -> intro_pattern
    | patAnd : intro_pattern -> intro_pattern -> intro_pattern
    | patOr : intro_pattern -> intro_pattern -> intro_pattern.

  Fixpoint read_name s := match s with
  | String "]" s' => ("", String "]" s')
  | String " " s' => ("", String " " s')
  | String "|" s' => ("", String "|" s')
  | String c s' => let (a, s'') := read_name s' in (String c a, s'')
  | EmptyString => ("", EmptyString)
  end.

  Fixpoint parse_intro_pattern' s fuel := match fuel with
  | 0 => (None, s)
  | S fuel' =>
    match s with
    | String ("[") s' => 
        match parse_intro_pattern' s' fuel' with
        | (Some p1, String "|" s'') => match parse_intro_pattern' s'' fuel' with
                                      | (Some p2, String "]" s''') => (Some (patOr p1 p2), s''')
                                      | _ => (None, "")
                                      end
        | (Some p1, String " " s'') => match parse_intro_pattern' s'' fuel' with
                                      | (Some p2, String "]" s''') => (Some (patAnd p1 p2), s''')
                                      | _ => (None, "")
                                      end
        | _ => (None, "")
        end
      | String ("]") s' => (Some (patId "?"), String "]" s')
      | String " " s' => (Some (patId "?"), String " " s')
      | String "|" s' => (Some (patId "?"), String "|" s')
      | EmptyString => (None, EmptyString)
      | s => let (a, s') := read_name s in (Some (patId a), s')
    end
  end.
  Definition parse_intro_pattern s := fst (parse_intro_pattern' s 100).

End IntroPattern.



(** Basic tactics *)

Ltac ctx := make_compatible ltac:(fun _ _ => apply Ctx; firstorder).

Ltac fexfalso := make_compatible ltac:(fun _ _ => apply Exp).
Ltac fsplit := make_compatible ltac:(fun _ _ => apply CI).
Ltac fleft := make_compatible ltac:(fun _ _ => apply DI1).
Ltac fright := make_compatible ltac:(fun _ _ => apply DI2).





(* 
 * [fintro], [fintros] 
 * 
 * Similar to Coq. Identifiers need to be given as strings (e.g. 
 * [fintros "H1" "H2"]). With "?" you can automatically generate
 * a name (e.g. [fintros "?" "H"]).
 * 
 * Now also handles intro patterns! For now unneccessary spaces
 * are not alowed in intro patterns. E.g. instead of "[H1 | H2]",
 * write "[H1|H2]".
 *)

Section FullLogic.
  Variable p : peirce.

  Lemma intro_and_destruct A s t G :
    A ⊢ (s --> t --> G) -> A ⊢ (s ∧ t --> G).
  Proof.
    intros. now apply switch_conj_imp.
  Qed.

  Lemma intro_or_destruct A s t G :
    A ⊢ (s --> G) -> A ⊢ (t --> G) -> A ⊢ (s ∨ t --> G).
  Proof.
    intros Hs Ht. apply II. eapply DE. ctx. 
    eapply Weak in Hs. eapply IE. apply Hs. ctx. firstorder.
    eapply Weak in Ht. eapply IE. apply Ht. ctx. firstorder.
  Qed.
End FullLogic.

(* After ∀-intro, the context gets turned into `map (subst_form ↑) C`.
 * This tactic behaves like [cbn], except that it doesn't go into
 * `cblackbox` terms. *)
Ltac simpl_map_subst C :=
  match C with
  | map (subst_form ?s) cnil => constr:(cnil)
  | map (subst_form ?s) (ccons ?a ?t ?C') => 
      let t' := eval cbn in (subst_form s t) in 
      let C'' := simpl_map_subst (map (subst_form s) C') in
      constr:(ccons a t' C'')
  | map (subst_form ?s) (cblackbox ?A) =>
      (* Test if we can drop the `map` because all identifiers 
       * are bound insinde (as is the case in `FA`).
       * The hack of matching on goal allows tactic execution
       * although this tactic has a return value. *)
      let check := match goal with _ => 
        let H := fresh in assert (C = A) as H by reflexivity; clear H end in
      constr:(cblackbox A)
  | _ => C
  end.

Ltac fintro'' intro_pat :=
  match intro_pat with
  | patAnd ?p1 ?p2 => 
      make_compatible ltac:(fun _ _ => apply intro_and_destruct);
      fintro'' p1; fintro'' p2
  | patOr ?p1 ?p2 =>
      make_compatible ltac:(fun _ _ => apply intro_or_destruct);
      [fintro'' p1 | fintro'' p2]
  | patId ?id =>
      match goal with 
      | [ |- ?A ⊢ ∀ ?t ] => apply AllI
      | [ |- ?A ⊢ (?s --> ?t) ] => apply II
      (* Special care for intro in proof mode *)
      | [ |- pm ?V ?C (∀ ?t) ] => make_compatible ltac:(fun _ _ => apply AllI)
      | [ |- pm ?V ?C (named_quant All _ ?t) ] =>
          apply AllI;
          let name := 
            match id with 
            | "?" => new_name "x" V
            | _ => match lookup V id with
              | @None => id
              | @Some _ _ => let msg := eval cbn in ("Identifier already used: " ++ id) in fail 6 msg
              end
            end
          in let C' := simpl_map_subst (map (subst_form ↑) C) in
          change (pm (vcons name V) C' t);
          update_binder_names
      | [ |- pm ?V ?C (?s --> ?t) ] =>
          apply II;
          let name := 
            match id with 
            | "?" => new_name "H" C
            | _ => match lookup C id with
              | @None => id
              | @Some _ _ => let msg := eval cbn in ("Identifier already used: " ++ id) in fail 6 msg
              end
            end
          in change (pm V (ccons name s C) t)
      end
  end.
Ltac fintro' intro_pat := 
  match eval cbn in (parse_intro_pattern intro_pat) with
  | Some ?p => fintro'' p
  | None => let msg := eval cbn in ("Invalid intro pattern: " ++ intro_pat) in fail 2 msg
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

Tactic Notation "ctx2hyp" integer(n) "as" reference(H) := make_compatible ltac:(fun _ _ => ctx2hyp' n H).





(* Spimplify terms that occur during specialization *)
Ltac simpl_subst_hyp H :=
  cbn in H;
  repeat match type of H with
  | context C[subst_term ?s ?t] => let H' := context C[t[s]] in change H' in H
  end;
  repeat match type of H with
  | context C[?t[S >> var]] => let H' := context C[t[↑]] in change H' in H
  end;
  try rewrite !up_term in H;
  try rewrite !subst_term_shift in H;
  (* Domain specific simplifications: *)
  try fold zero in H.

Ltac simpl_subst_goal :=
  cbn;
  repeat match goal with
  | [ |- context C[subst_term ?s ?t] ] => let G := context C[t[s]] in change G
  end;
  repeat match goal with
  | [ |- context C[?t[S >> var]] ] => let G := context C[t[↑]] in change G
  end;
  try rewrite !up_term;
  try rewrite !subst_term_shift;
  (* Domain specific simplifications: *)
  try fold zero.

Tactic Notation "simpl_subst" hyp(H) := (simpl_subst_hyp H).
Tactic Notation "simpl_subst" := (simpl_subst_goal).







(* 
 * [fspecialize (H x1 x2 ... xn)], [fspecialize H with x1 x2 ... xn] 
 * 
 * Specializes a Coq hypothesis `H` of the form `X ⊢ ∀∀...∀ p1 --> ... --> pn --> g`
 * with `x1, x2, ..., xn`.
 *)

Ltac fspecialize_list H A var_names := 
  match A with
  | [] => simpl_subst H
  | ?a::?A' => 
      let x := match type of a with
        | string => match lookup var_names a with  (* Free variable name *)
          | @None => let msg := eval cbn in ("Unknown identifier: " ++ a) in fail 10 msg
          | @Some _ ?n => constr:($n)
          end
        | _ => a
        end 
      in tryif 
        apply (fun H => IE _ _ _ H x) in H
      then idtac
      else (
        (* For some reason we cannot directly [apply (AllE _ x)]
           if x contains ⊕, σ, etc. But evar seems to work. *)
        let x' := fresh "x" in 
        eapply (AllE _ ?[x']) in H; 
        instantiate (x' := x) );
    fspecialize_list H A' var_names
  end.

Tactic Notation "fspecialize" "(" hyp(H) constr(x1) ")" := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1]) V).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) ")" := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1; x2]) V).
Tactic Notation "fspecialize" "(" hyp(H) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1;x2;x3]) V).

Tactic Notation "fspecialize" hyp(H) "with" constr(x1) := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1]) V).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1;x2]) V).
Tactic Notation "fspecialize" hyp(H) "with" constr(x1) constr(x2) constr(x3) := make_compatible ltac:(fun _ V => fspecialize_list H constr:([x1;x2;x3]) V).




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

(* Check wether T is a hypothesis, a context index, a context formula
 * or a context name and put it into hypothesis H. *)
Ltac turn_into_hypothesis T H contxt := 
  tryif is_hyp T
  then assert (H := T)  (* Hypothesis *)
  else match goal with [ |- ?C ⊢ _ ] => 
    match type of T with
    | form => assert (C ⊢ T) as H by ctx  (* Explicit form *)
    | nat => let T' := nth C T in assert (C ⊢ T') as H by ctx  (* Idx in context *)
    | string => match lookup contxt T with  (* Context name *)
      | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
      | @Some _ ?n => let T' := nth C n in assert (C ⊢ T') as H by ctx
      end
    end
  end.

(* If `H` has the type `P1 -> P2 -> ... -> Pn -> (A ⊢ ϕ)`, this
 * tactic adds goals for `P1, P2, ..., Pn` and specializes `H`. *)
Ltac assert_premises H :=
  match type of H with
  | _ ⊢ _ => idtac
  | pm _ _ _ => idtac
  | ?A -> ?B => 
      let H' := fresh "H" in assert A as H';
      [|specialize (H H'); clear H'; assert_premises H ]
  end.

Ltac feapply' T A := fun contxt free_vars =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` containes has further Coq premises before the formula 
   * statement, we add them as additional goals. *)
  assert_premises H;
  (* Match on the goal, so that we don't try to apply to these
   * additional goals. *)
  match goal with
  | [ |- _ ⊢ _ ] =>
    fspecialize_list H A free_vars;
    instantiate_evars H;
    simpl_subst H;
    match goal with [ |- ?C ⊢ _ ] => 
      eapply (Weak _ C) in H; [| firstorder]
    end;
    fapply_without_quant H; 
    (* [fapply_without_quant] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals
  | [ |- _ ] => idtac
  end;
  clear H.

Ltac fapply' T A contxt free_vars :=
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` containes has further Coq premises before the formula 
   * statement, we add them as additional goals. *)
   assert_premises H;
   (* Match on the goal, so that we don't try to apply to these
    * additional goals. *)
   match goal with
   | [ |- _ ⊢ _ ] =>
    fspecialize_list H A free_vars; 
    instantiate_evars H; 
    simpl_subst H;
    match goal with [ |- ?U ⊢ _ ] => 
      eapply (Weak _ U) in H; [| firstorder]
    end;
    fapply_without_quant H;
    (* [fapply_without_quant] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals;
    (* Evars should only be used for unification in [fapply].
     * Therefore reject, if there are still evars visible. *)
    (* TODO: This is not optimal. If the goal contains evars, 
     * H might still contain evars after unification and we would fail. *)
    tryif has_evar ltac:(type of H) 
    then fail 3 "Cannot find instance for variable. Try feapply?" 
    else clear H
  | [ |- _ ] => idtac
  end;
  try clear H.


Tactic Notation "feapply" constr(T) := make_compatible ltac:(feapply' T constr:([] : list form)).
Tactic Notation "feapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(feapply' T constr:([x1])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(feapply' T constr:([x1;x2])).
Tactic Notation "feapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(feapply' T constr:([x1;x2;x3])).

Tactic Notation "fapply" constr(T) := make_compatible ltac:(fapply' T constr:([] : list form)).
Tactic Notation "fapply" "(" constr(T) constr(x1) ")" := make_compatible ltac:(fapply' T constr:([x1])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) ")" := make_compatible ltac:(fapply' T constr:([x1;x2])).
Tactic Notation "fapply" "(" constr(T) constr(x1) constr(x2) constr(x3) ")" := make_compatible ltac:(fapply' T constr:([x1;x2;x3])).




(*
 * [fassert phi], [fassert phi as "H"]
 *
 * Similar to coq. Also supports intro patterns.
 *)

Section FullLogic.
  Variable p : peirce.

  Lemma fassert_help A phi psi :
    A ⊢ phi -> A ⊢ (phi --> psi) -> A ⊢ psi.
  Proof.
    intros H1 H2. eapply IE. exact H2. exact H1.
  Qed.
End FullLogic.
Arguments fassert_help {_} _ _ _.

Ltac fassert' phi := fun _ _ =>
match goal with
| [ |- ?A ⊢ ?psi ] =>
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  assert (A ⊢ phi) as H1; [ | 
    assert (A ⊢ (phi --> psi)); [ clear H1 |
      apply (fassert_help A phi psi H1 H2)
    ]
  ]
end.

Tactic Notation "fassert" constr(phi) := (make_compatible ltac:(fassert' phi)); [| fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) := (make_compatible ltac:(fassert' phi)); [| fintro H].
Tactic Notation "fassert" constr(phi) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro H].





(*
 * [fdestruct H], [fdestruct H as "pattern"]
 *
 * Destructs an assumption into the ND context. Works on
 * - Coq hypothesis by name
 * - Formula in in ND context by index (e.g. [fdestruct 3])
 * - Name of a context assumption in proof mode (e.g. [fdestruct "H2"])
 *)

Ltac fdestruct' n pat :=
  match n with
  | 0 => 
      match goal with 
      | [ |- prv _ _ ] => apply -> switch_imp; fintro'' pat
      | [ |- pm ?V (ccons _ ?t ?C) ?phi ] =>
          apply -> switch_imp; change (pm V C (t --> phi)); fintro'' pat
      end
  | S ?n' =>
      match goal with 
      | [ |- prv _ _ ] => apply -> switch_imp; fdestruct' n' pat; apply <- switch_imp
      | [ |- pm ?V (ccons ?a ?t ?C) ?phi ] => 
          apply -> switch_imp; change (pm V C (t --> phi)); fdestruct' n' pat;
          match goal with [ |- pm ?V ?C' (t --> phi) ] => 
            apply <- switch_imp; change (pm V (ccons a t C') phi)
          end
      end
  end.

Ltac create_pattern T :=
  match T with
  | ?t ∧ ?s =>
    let p1 := create_pattern t in
    let p2 := create_pattern s in
    constr:(patAnd p1 p2)
  | ?t ∨ ?s =>
    let p1 := create_pattern t in
    let p2 := create_pattern s in
    constr:(patOr p1 p2)
  | _ => constr:(patId "?")
  end.

Ltac fdestruct'' T pat :=
  tryif is_hyp T then (
    let H := fresh "H" in
    let X := fresh "X" in
    assert (H := T);
    match goal with
    | [ |- prv ?A ?t ] => 
        match type of H with 
        | prv _ ?s => enough (A ⊢ (s --> t)) as X by (feapply X; feapply H)
        | pm _ _ ?s => enough (A ⊢ (s --> t)) as X by (feapply X; feapply H)
        end
    | [ |- pm ?V ?A ?t ] =>
        match type of H with 
        | prv _ ?s => enough (pm V A (s --> t)) as X by (feapply X; feapply H)
        | pm _ _ ?s => enough (pm V A (s --> t)) as X by (feapply X; feapply H)
        end
    end;
    fintro "?"; fdestruct'' 0 pat; clear H
  )
  else (
    let n := match type of T with 
      | nat => T 
      | string => match goal with [ |- pm ?V ?C _ ] => 
        match lookup C T with 
        | @Some _ ?n' => n'
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 3 msg
        end
      end
    end in
    let pattern := lazymatch pat with
      | "" => 
        match goal with 
        | [ |- prv ?A _ ] => let t := nth A n in create_pattern t 
        | [ |- pm _ ?C _ ] => let t := nth C n in create_pattern t 
        end
      | _ => 
        match eval cbn in (parse_intro_pattern pat) with 
        | @Some _ ?p => p
        | @None => let msg := eval cbn in ("Invalid pattern: " ++ pat) in fail 3 msg
        end
    end in fdestruct' n pattern
  ).

Tactic Notation "fdestruct" constr(T) := fdestruct'' T "".
Tactic Notation "fdestruct" constr(T) "as" constr(pat) := fdestruct'' T pat.






Section FullLogic.

  Variable p : peirce.


  (* Basic tactics *)
  Ltac freflexivity := fapply ax_refl.



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



  Lemma leibniz_term (t t' s : term) :
    FA ⊢ (t == t' --> s[t..] == s[t'..]).
  Proof.
    fintros. induction s; cbn.
    - destruct x; cbn. ctx. freflexivity.
    - destruct F; repeat depelim v; cbn.
      * freflexivity.
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
        (* enough (forall u1 u2, FA ⊢ ((∀ phi[u1][up t..][u2]) --> (∀ phi[u1][up t'..][u2]))).
        { specialize (H0 var var). now rewrite !subst_var in H0. }
        assert (forall (t t' : term) u1 u2, FA ⊢ (t == t') -> FA ⊢ (phi[u1][t..][u2] --> phi[u1][t'..][u2])) as IH' by admit. *)

        intros. fintros. 
        change (((∀ phi)[t..][↑] :: map (subst_form ↑) A) ⊢ phi[up t'..]).
        change ((∀ phi[up t..][up ↑] :: map (subst_form ↑) A) ⊢ phi[up t'..]).
        (* ? *)
  Admitted.




  Fixpoint up_n n sigma := match n with
  | 0 => sigma
  | S n' => up (up_n n' sigma)
  end.

  Ltac shift_n n t := 
    match n with
    | 0 => t
    | S ?n' => shift_n n' (t[↑])
    end.

  Ltac vector_map_ltac v f :=
    match v with
    | Vector.nil _ => constr:(Vector.nil term)
    | Vector.cons ?x ?v => 
      let x' := f x in 
      let v' := vector_map_ltac v f in
      constr:(Vector.cons x' v')
    end.

  (* Returns a new formula where all occurences of `t` are turned into
   * `($n)[up_n n t..]` and every other term `s` into `s[up_n n ↑][up_n t..]`,
   * where `n` is the quantor depth. *)
  Ltac add_shifts' n t G :=
    let f := add_shifts' n t in 
    let t_shifted := shift_n n t in
    match G with
    (* Terms: *)
    | t_shifted => constr:(($n)[up_n n t..])
    | $(?m) => constr:(($m)[up_n n ↑][up_n n t..])
    | func ?fu ?vec => let vec' := vector_map_ltac vec f in constr:(func fu vec')
    (* Formulas: *)
    | fal => constr:(fal[up_n n ↑][up_n n t..])
    | atom ?P ?vec => let vec' := vector_map_ltac vec f in constr:(atom P vec')
    | bin ?op ?u ?v => let u' := f u in let v' := f v in constr:(bin op u' v')
    | quant ?op ?u => let u' := add_shifts' (S n) t u in constr:(quant op u')
    (* Fallback for variables which cannot be matched syntactically: *)
    | ?u => constr:(u[up_n n ↑][up_n n t..])
    end.
  Ltac add_shifts := add_shifts' 0.

  (* Returns a new formula where all occurences of `s[up_n n ↑][up_n nt..]` 
   * in G are turned into `s[up_n n ↑]` and `($n)[up_n n t..]` into `$n`. *)
  Ltac remove_shifts G t :=
    match G with 
    | context C[ ?s[up_n ?n ↑][up_n ?n t..] ] => let G' := context C[ s[up_n n ↑] ] in remove_shifts G' t
    | context C[ ($ ?n)[up_n ?n t..] ] => let G' := context C[ $n ] in remove_shifts G' t
    | _ => G
    end.

  Ltac frewrite' T A back := fun contxt free_vars =>
    let H := fresh "H" in
    turn_into_hypothesis T H contxt;
    fspecialize_list H A free_vars; 
    instantiate_evars H; 
    simpl_subst H;
    match type of H with _ ⊢ (?_t == ?_t') =>
      let t := match back with true => _t' | false => _t end in
      let t' := match back with true => _t | false => _t' end in

      (* 1. Replace each occurence of `t` with `($n)[up_n n t..]` and every
       *  other `s` with `s[up_n n ↑][up_n n t..]`. The new formula is 
       *  created with the [add_shifts] tactic and proven in place. *)
      match goal with [ |- ?C ⊢ ?G ] => 
        let X := fresh in 
        let G' := add_shifts t G in
        enough (C ⊢ G') as X;
        [
          repeat match type of X with context K[ ?u[up_n ?n ↑][up_n ?n t..] ] =>
            let R := fresh in
            (* TODO: Prove general lemma for this: *)
            assert (u[up_n n ↑][up_n n t..] = u) as R; [
              rewrite subst_term_comp; apply subst_term_id; 
              let a := fresh in intros a;
              (do 10 try destruct a); reflexivity |];
            rewrite R in X
          end;
          apply X
        |]
      end;

      (* 2. Pull out the [t..] substitution *)
      match goal with [ |- ?U ⊢ ?G ] =>
        let G' := remove_shifts G t in change (U ⊢ G'[t..])
      end;
      
      (* 3. Change [t..] to [t'..] using leibniz. For some reason
       *  we cannot directly [apply leibniz with (t := t')] if t'
       *  contains ⊕, σ, etc. But evar seems to work. *)
      let t'' := fresh "t" in 
      eapply (leibniz _ _ ?[t'']);
      [ instantiate (t'' := t'); firstorder |
        match back with
        | false => feapply ax_sym; fapply H
        | true => apply H
        end
      | ];
      
      (* 4. Pull substitutions inward, but don't unfold `up_n` *)
      cbn -[up_n];

      (* 5. Turn subst_term calls back into []-Notation *)
      repeat match goal with [ |- context C[subst_term ?sigma ?s] ] =>
        let G' := context C[ s[sigma] ] in change G'
      end;

      (* 6. Fix simplification that occurs because of cbn *)
      repeat match goal with [ |- context C[up_n ?n ↑ ?a] ] =>
        let G' := context C[ ($a)[up_n n ↑] ] in change G'
      end;

      (* 7. Change `up (up ...)` back into `up_n n ...` *)
      repeat match goal with 
      | [ |- context C[up_n ?n (up ?s)]] => let G' := context C[up_n (S n) s] in change G'
      | [ |- context C[up ?s]] => let G' := context C[up_n 1 s] in change G'
      end;

      (* 6. Simplify *)
      repeat match goal with [ |- context K[ ?u[up_n ?n ↑][up_n ?n t'..] ]] =>
        let R := fresh in
        (* TODO: Prove general lemma for this: *)
        assert (u[up_n n ↑][up_n n t'..] = u) as R; [
          rewrite subst_term_comp; apply subst_term_id; 
          let a := fresh in intros a;
          (do 10 try destruct a); reflexivity |];
        rewrite ! R;
        clear R
      end;

      (* Base case for rewrite without quantors *)
      cbn; try rewrite !subst_shift; try rewrite !subst_term_shift;

      (* Use notation *)
      repeat match goal with [ |- context C[S >> var] ] =>
        let G' := context C[↑] in change G'
      end;
      try fold zero
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



  (* Rewrite under quantors: *)

  Goal forall t t', FA ⊢ (t == t') -> FA ⊢ ∀ $0 ⊕ σ t[↑] == t' ⊕ σ $0.
  Proof.
    intros. frewrite H. 
  Abort.

  Goal forall t t', FA ⊢ (t == t') -> FA ⊢ ∀∃ $0 ⊕ σ t == t'[↑][↑] ⊕ σ $0.
  Proof.
    intros. frewrite <- H. 
  Abort.



  (* Variable names instead of de Bruijn: *)
  Goal FA ⊢ ∀ ∀ $1 == $0 --> $1 == zero ⊕ $0.
  Proof.
    fstart. hnf. fstart. fintros "x" "y" "H". frewrite "H". frewrite (ax_add_zero "y").
    fapply ax_refl.
  Qed.




  (* XM for closed, quantor free formulas: *)

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
  


