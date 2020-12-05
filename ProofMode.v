Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import Theories.
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

Definition pm {p cf cp} C phi := @prv p cf cp C phi.
Arguments pm {_} {_} {_} _ _.

Definition tpm {p cf cp} C phi := @tprv p cf cp C phi.
Arguments tpm {_} {_} {_} _ _.

Section PM.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.

Definition cnil := @nil form.
Definition ccons (s : string) phi C := @cons form phi C.
(* Special alias for unknown lists. Only used to indent with one space in Notation *)
Definition cblackbox (A : list form) := A.

Definition tnil : theory := fun _ => False.
Definition tcons (s : string) phi (T : theory) : theory := extend T phi.
(* Special alias for unknown theories. Only used to indent with one space in Notation *)
Definition tblackbox (T : theory) := T.

End PM.


(* Dummy tactic the end user *must* override if defined
 * terms like `zero` are used. *)
Ltac custom_fold := idtac.

(* Dummy tactic the end user *must* override if defined
 * terms like `zero` are used. *)
 Ltac custom_unfold := idtac.

(* Dummy tactic the end user can override to add domain
 * specific simplifications. *)
Ltac custom_simpl := idtac.



(** Overload deduction rules to also work for theories: *)

Class DeductionRules `{funcs_signature, preds_signature} (context : Type) (ent : context -> form -> Type) (cons : form -> context -> context) (map : (form -> form) -> context -> context) (In : form -> context -> Prop) :=
{
  II A phi psi : ent (cons phi A) psi -> ent A (phi --> psi) ;
  IE A phi psi : ent A (phi --> psi) -> ent A phi -> ent A  psi ;
  AllI A phi : ent (map (subst_form ↑) A) phi -> ent A (∀ phi) ;
  AllE A t phi : ent A (∀ phi) -> ent A (phi[t..]) ;
  ExI A t phi : ent A (phi[t..]) -> ent A (∃ phi) ;
  ExE A phi psi : ent A (∃ phi) -> ent (cons phi (map (subst_form ↑) A)) (psi[↑]) -> ent A psi ;
  Exp A phi : ent A ⊥ -> ent A phi ;
  Ctx A phi : In phi A -> ent A phi ;
  CI A phi psi : ent A phi -> ent A psi -> ent A (phi ∧ psi) ;
  CE1 A phi psi : ent A (phi ∧ psi) -> ent A phi ;
  CE2 A phi psi : ent A (phi ∧ psi) -> ent A psi ;
  DI1 A phi psi : ent A phi -> ent A (phi ∨ psi) ;
  DI2 A phi psi : ent A psi -> ent A (phi ∨ psi) ;
  DE A phi psi theta : ent A (phi ∨ psi) -> ent (cons phi A) theta -> ent (cons psi A) theta -> ent A theta ;
}.

Class ClassicalDeductionRules `{funcs_signature, preds_signature} (context : Type) (ent : context -> form -> Type) :=
{
  Pc A phi psi : ent A (((phi --> psi) --> phi) --> phi)
}.

Class WeakClass `{funcs_signature, preds_signature} (context : Type) (ent : context -> form -> Type) (incl : context -> context -> Prop) :=
{
  Weak A B phi : ent A phi -> incl A B -> ent B phi
}.

Instance prv_DeductionRules `{funcs_signature, preds_signature, peirce} : DeductionRules (list form) prv cons (@List.map form form) (@In form) := 
{| 
  II := Deduction.II ;
  IE := Deduction.IE ;
  AllI := Deduction.AllI ;
  AllE := Deduction.AllE ;
  ExI := Deduction.ExI ;
  ExE := Deduction.ExE ;
  Exp := Deduction.Exp ;
  Ctx := Deduction.Ctx ;
  CI := Deduction.CI ;
  CE1 := Deduction.CE1 ;
  CE2 := Deduction.CE2 ;
  DI1 := Deduction.DI1 ;
  DI2 := Deduction.DI2 ;
  DE := Deduction.DE ;
|}.

Instance prv_ClassicalDeductionRules `{funcs_signature, preds_signature} : ClassicalDeductionRules (list form) (@prv _ _ class) := 
{| 
  Pc := Deduction.Pc
|}.

Instance prv_WeakClass `{funcs_signature, preds_signature, peirce} : WeakClass (list form) prv (@List.incl form) := 
{| 
  Weak := Deduction.Weak
|}.

Instance tprv_DeductionRules `{funcs_signature, preds_signature, peirce} : DeductionRules theory tprv (fun a b => extend b a) mapT (fun a b => in_theory b a) := 
{| 
  II := Theories.T_II ;
  IE := Theories.T_IE ;
  AllI := Theories.T_AllI ;
  AllE := Theories.T_AllE ;
  ExI := Theories.T_ExI ;
  ExE := Theories.T_ExE ;
  Exp := Theories.T_Exp ;
  Ctx := Theories.T_Ctx ;
  CI := Theories.T_CI ;
  CE1 := Theories.T_CE1 ;
  CE2 := Theories.T_CE2 ;
  DI1 := Theories.T_DI1 ;
  DI2 := Theories.T_DI2 ;
  DE := Theories.T_DE ;
|}.

Instance tprv_ClassicalDeductionRules `{funcs_signature, preds_signature} : ClassicalDeductionRules theory (@tprv _ _ class) := 
{| 
  Pc := Theories.T_Pc
|}.

Instance tprv_WeakClass `{funcs_signature, preds_signature, peirce} : WeakClass theory tprv subset_T := 
{| 
  Weak := Theories.WeakT
|}.



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
  | tcons name _ _ => constr:(Some n) 
  | tcons _ _ ?T' => lookup' (S n) T' name
  | _ => None
  end.
Ltac lookup := lookup' 0.

Ltac nth A n :=
  match n with
  | 0 => match A with ?t :: _ => t | extend _ ?t => t | ccons _ ?t _ => t | tcons _ ?t _ => t end
  | S ?n' => match A with _ :: ?A' => nth A' n' | extend ?A' _ => nth A' n' | ccons _ _ ?A' => nth A' n' | tcons _ _ ?T' => nth T' n' end
  end.

Ltac map_ltac A f :=
  match A with
  | nil => constr:(nil)
  | cnil => constr:(cnil)
  | tnil => constr:(tnil)
  | @Vector.nil ?a => constr:(@Vector.nil a)
  | cblackbox ?A' => A
  | tblackbox ?A' => A
  | cons ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(cons x' A'')
  | ccons ?s ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(ccons s x' A'')
  | tcons ?s ?x ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(tcons s x' A'')
  | @Vector.cons _ ?x _ ?A' => let x' := f x in let A'' := map_ltac A' f in constr:(@Vector.cons _ x' _ A'')
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
  | extend ?T' ?phi =>
    let x := create_context' T' in match x with (?c, ?n) =>
      match n with
        | 0 => constr:((tcons "H" phi c, S n))
        | S ?n' => let s' := eval cbn in ("H" ++ nat_to_string n') in constr:((tcons s' phi c, S n))
      end
    end
  | nil => constr:((cnil, 0))
  | _ => 
    (* If it's not a cons or nil, it's a variable/function call/... 
     * and we don't want to look into it *)
    match type of A with
    | list form => constr:((cblackbox A, 0))
    | theory => constr:((tblackbox A, 0))
    | form -> Prop => constr:((tblackbox A, 0))
    end
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
  match goal with 
  | [ |- @pm _ _ ?p ?C ?phi ] =>
    let f := constr:(fun (n : nat) => "ERROR") in
    let annotate_form := annotate_form' f 0 in
    let phi' := annotate_form phi in
    let C' := map_ltac C annotate_form in
    change (@pm _ _ p C' phi')
  | [ |- @tpm _ _ ?p ?C ?phi ] =>
    let f := constr:(fun (n : nat) => "ERROR") in
    let annotate_form := annotate_form' f 0 in
    let phi' := annotate_form phi in
    let C' := map_ltac C annotate_form in
    change (@tpm _ _ p C' phi')
  end.
Ltac update_binder_names := unfold named_quant; unfold named_var; add_binder_names.



Notation "" := cnil (only printing).
Notation "A" := (cblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (ccons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Notation "" := tnil (only printing).
Notation "A" := (tblackbox A) (at level 1, only printing, format " A").
Notation "C name : phi" := (tcons name phi C)
  (at level 1, C at level 200, phi at level 200,
  left associativity, format "C '//'  name  :  '[' phi ']'", only printing).

Notation "∀ x .. y , phi" := (named_quant All x ( .. (named_quant All y phi) .. )) (at level 50, only printing,
  format "'[' '∀'  '/  ' x  ..  y ,  '/  ' phi ']'").
Notation "∃ x .. y , phi" := (named_quant Ex x ( .. (named_quant Ex y phi) .. )) (at level 50, only printing,
  format "'[' '∃'  '/  ' x  ..  y ,  '/  ' phi ']'").

Notation "x" := (named_var x) (at level 1, only printing).

Notation "C '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (pm C phi)
  (at level 1, left associativity,
  format " C '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).

Notation "T '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' phi" :=
  (tpm T phi)
  (at level 1, left associativity,
  format " T '//' '━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━' '//'  phi", only printing).


(* Tactics to toggle proof mode *)
Ltac fstart := 
  match goal with 
  | [ |- @prv _ _ ?p ?A ?phi ] => let C := create_context A in change (@pm _ _ p C phi)
  | [ |- @tprv _ _ ?p ?T ?phi ] => let C := create_context T in change (@tpm _ _ p C phi)
  end;
  add_binder_names.
Ltac fstop := 
  match goal with 
  | [ |- @pm _ _ ?p ?C ?phi ] => change (@prv _ _ p C phi)
  | [ |- @tpm _ _ ?p ?C ?phi ] => change (@tprv _ _ p C phi)
  end;
  unfold pm in *; unfold cnil; unfold ccons;unfold cblackbox; 
  unfold tpm in *; unfold tnil; unfold tcons;unfold tblackbox; 
  unfold named_quant; unfold named_var.


(* All the tactics defined below work with the original `prv` type.
 * The following tactic lifts them to be compatible with `pm`.
 *
 * Every tactic must have an additional argument where the current
 * context is filled in if the proof mode is active, and `cnil` 
 * otherwise. *)
Ltac make_compatible tac :=
  match goal with
  | [ |- prv ?A _ ] => tac A
  | [ |- tprv ?T _ ] => tac T
  | [ |- @pm _ _ ?p ?C _ ] => 
      fstop; 
      tac C;
      match goal with 
      | [ |- pm _ _ ?G ] => change (@pm _ _ p C G) 
      | [ |- prv _ ?G ] => change (@pm _ _ p C G)
      | _ => idtac 
      end;
      try update_binder_names (* [try] because some tactics add normal Coq goals *)
  | [ |- @tpm _ _ ?p ?C _ ] => 
      fstop;
      tac C;
      match goal with 
      | [ |- tprv _ ?G ] => change (@tpm _ _ p C G)
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





(* Spimplify terms that occur during specialization *)
Ltac simpl_subst_hyp H :=
  cbn in H;
  (* repeat match type of H with
  | context C[subst_term ?s ?t] => let H' := context C[t[s]] in change H' in H
  end;
  repeat match type of H with
  | context C[subst_form ?s ?t] => let H' := context C[t[s]] in change H' in H
  end; *)
  repeat match type of H with
  | context C[S >> var] => let H' := context C[↑] in change H' in H
  end;
  try rewrite !up_term in H;
  try rewrite !subst_term_shift in H;
  (* Turn `(S >> var) 4` into `$5`. TODO: Find a better way to do this. *)
  unfold ">>";
  (* Domain specific simplifications: *)
  custom_fold;
  custom_simpl.

Ltac simpl_subst_goal :=
  cbn;
  (* repeat match goal with
  | [ |- context C[subst_term ?s ?t] ] => let G := context C[t[s]] in change G
  end;
  repeat match goal with
  | [ |- context C[subst_form ?s ?t] ] => let G := context C[t[s]] in change G
  end; *)
  repeat match goal with
  | [ |- context C[S >> var] ] => let G := context C[↑] in change G
  end;
  try rewrite !up_term;
  try rewrite !subst_term_shift;
  (* Turn `(S >> var) 4` into `$5`. TODO: Find a better way to do this. *)
  unfold ">>";
  (* Domain specific simplifications: *)
  custom_fold;
  custom_simpl.

Tactic Notation "simpl_subst" hyp(H) := (simpl_subst_hyp H).
Tactic Notation "simpl_subst" := (simpl_subst_goal).


(* Return the context of the goal or a hypothesis *)
Ltac get_context_goal :=
  match goal with
  | [ |- ?C ⊢ _ ] => C
  | [ |- ?C ⊩ _ ] => C
  | [ |- pm ?C _ ] => C
  | [ |- tpm ?C _ ] => C
  end.
Ltac get_context_hyp H :=
  match type of H with
  | ?C ⊢ _ => C
  | ?C ⊩ _ => C
  | pm ?C _ => C
  | tpm ?C _ => C
  end.
Tactic Notation "get_context" := get_context_goal.
Tactic Notation "get_context" hyp(H) := get_context_hyp H.


(* Return the formula inside the goal or a hypothesis *)
Ltac get_form_goal :=
  match goal with
  | [ |- _ ⊢ ?phi ] => phi
  | [ |- _ ⊩ ?phi ] => phi
  | [ |- pm _ ?phi ] => phi
  | [ |- tpm _ ?phi ] => phi
  end.
Ltac get_form_hyp H :=
  match type of H with
  | _ ⊢ ?phi => phi
  | _ ⊩ ?phi => phi
  | pm _ ?phi => phi
  | tpm _ ?phi => phi
  end.
Tactic Notation "get_form" := get_form_goal.
Tactic Notation "get_form" hyp(H) := get_form_hyp H.





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
 * a name (e.g. [fintros "?" "H"]).
 * 
 * Now also handles intro patterns! For now unneccessary spaces
 * are not alowed in intro patterns. E.g. instead of "[H1 | H2]",
 * write "[H1|H2]".
 *)

Section Fintro.
  Context {Σ_funcs : funcs_signature}.  
  Context {Σ_preds : preds_signature}.
  Variable p : peirce.

  (* Lemmas for alternative ∀-intro and ∃-application.
   * Taken from https://www.ps.uni-saarland.de/extras/fol-completeness/html/Undecidability.FOLC.FullND.html#nameless_equiv_all' *)
  Lemma nameless_equiv_all' A phi :
    exists t, A ⊢ phi[t..] <-> (map (subst_form ↑) A) ⊢ phi.
  Admitted.

  Lemma nameless_equiv_ex A phi psi :
    exists t, (psi[t..]::A) ⊢ phi <-> (psi::map (subst_form ↑) A) ⊢ phi[↑].
  Admitted.

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

  Lemma intro_and_destruct_T T s t G :
    T ⊩ (s --> t --> G) -> T ⊩ (s ∧ t --> G).
  Proof.
    intros. apply II. apply (IE _ t). apply (IE _ s).
    eapply Weak. apply H. firstorder.
    eapply CE1, Ctx; firstorder.
    eapply CE2, Ctx; firstorder.
  Qed.

  Lemma intro_or_destruct_T T s t G :
    T ⊩ (s --> G) -> T ⊩ (t --> G) -> T ⊩ (s ∨ t --> G).
  Proof.
    intros Hs Ht. apply II. eapply DE. ctx.
    eapply Weak in Hs. eapply IE. apply Hs. ctx. firstorder.
    eapply Weak in Ht. eapply IE. apply Ht. ctx. firstorder.
  Qed.

  Lemma subst_zero phi x :
    $0 = x -> phi = phi[fun n => match n with 0 => x | S n => $(S n) end].
  Proof.
    intros. symmetry. apply subst_id. intros [|]; cbn. now rewrite H. reflexivity.
  Qed.

  Lemma mapT_step f a T1 T2 :
    subset_T T1 (mapT f T2) -> subset_T (extend T1 (f a)) (mapT f (extend T2 a)).
  Proof.
    intros H psi H1. destruct H1 as [H1|H1].
    - destruct (H psi H1) as [rho [H2 H3]]. exists rho. split. now left. assumption.
    - exists a. split. now right. auto.
  Qed.

End Fintro.


Ltac name_from_pattern C id :=
  match id with 
  | "?" => new_name "H" C
  | _ => match lookup C id with
    | @None => id
    | @Some _ _ => let msg := eval cbn in ("Identifier already used: " ++ id) in fail 7 msg
    end
  end.

(* Syntactically evaluate `mapT f (T ⋄ a ⋄ b ⋄ c)` to
 * `(mapT f T) ⋄ f a ⋄ f b ⋄ f c` like it would happen using
 * [cbn] for map in normal lists. *)
Ltac eval_mapT M :=
  match M with
  | mapT ?f (extend ?T ?a) => let T' := eval_mapT (mapT f T) in constr:(extend T' (f a))
  | mapT ?f (tcons ?s ?a ?T) => let T' := eval_mapT (mapT f T) in constr:(tcons s (f a) T')
  | mapT ?f (tblackbox ?T) => constr:(tblackbox (mapT f T))
  | _ => M
  end.

(* Replace `mapT f (T ⋄ a ⋄ b ⋄ c)` in the context with 
 * `(mapT f T) ⋄ f a ⋄ f b ⋄ f c`. *)
Ltac simpl_context_mapT :=
  match goal with 
  | [ |- tprv ?T ?phi ] =>
      let T' := eval_mapT T in
      let X := fresh in
      enough (tprv T' phi) as X; [ 
        eapply Weak; [now apply X | repeat apply mapT_step; apply subset_refl ]
      |]
  | [ |- tpm ?T ?phi ] =>
      let T' := eval_mapT T in
      let X := fresh in
      enough (tpm T' phi) as X; [ 
        eapply Weak; [now apply X | repeat apply mapT_step; apply subset_refl ]
      |]
  end.

Ltac fintro_ident x :=
  let H := fresh "H" in
  match goal with
  | [ |- _ ⊢ ∀ ?t ] => 
    apply AllI;
    edestruct nameless_equiv_all' as [x H];
    apply H; clear H;
    simpl_subst
  | [ |- @pm _ _ ?p ?C (named_quant All _ ?t) ] =>
    apply AllI;
    edestruct nameless_equiv_all' as [x H];
    apply H; clear H;
    simpl_subst;
    match goal with [ |- prv _ ?t'] => change (@pm _ _ p C t') end;
    update_binder_names
  | [ |- _ ⊩ ∀ ?t ] =>
    let E := fresh "E" in
    apply AllI;
    assert (exists x, $0 = x) as [x E] by (now exists ($0));
    rewrite (subst_zero t x E); clear E;
    simpl_context_mapT;
    simpl_subst
  | [ |- @tpm _ _ ?p ?C (named_quant All _ ?t) ] =>
    let E := fresh "E" in
    apply AllI;
    assert (exists x, $0 = x) as [x E] by (now exists ($0));
    rewrite (subst_zero t x E); clear E;
    simpl_context_mapT;
    simpl_subst;
    update_binder_names
  | _ =>
    (* Unfold definitions to check if there are hidden ∀ underneath. 
     * Also perform simplification and fix names if the definition
     * does something nasty. *)
    progress custom_unfold; simpl_subst; try update_binder_names;
    custom_unfold; (* Unfold again because [simpl_subst] folds *)
    fintro_ident x;
    custom_fold
  end.

Ltac fintro_pat' pat :=
  match pat with
  | patAnd ?p1 ?p2 => (* Existential *)
      make_compatible ltac:(fun C =>
        apply II; eapply ExE; [ apply Ctx; now left |
          let x := fresh "x" in
          let H := fresh "H" in
          edestruct nameless_equiv_ex as [x H];
          apply H; clear H; cbn; simpl_subst; apply -> switch_imp;
          apply Weak with (A := C); [| firstorder] ]
      ); 
      fintro_pat' p2
  | patAnd ?p1 ?p2 => (* Conjunction *)
      make_compatible ltac:(fun _ => 
        match goal with 
        | [ |- prv _ _ ] => apply intro_and_destruct
        | [ |- tprv _ _ ] => apply intro_and_destruct_T
        end
      ); 
      fintro_pat' p1; fintro_pat' p2  
  | patOr ?p1 ?p2 =>
      make_compatible ltac:(fun _ => 
        match goal with 
        | [ |- prv _ _ ] => apply intro_or_destruct
        | [ |- tprv _ _ ] => apply intro_or_destruct_T
        end
      );
      [fintro_pat' p1 | fintro_pat' p2]
  | patId ?id =>
      match goal with 
      | [ |- ?A ⊢ ∀ ?t ] => let x := fresh "x" in fintro_ident x
      | [ |- ?A ⊩ ∀ ?t ] => let x := fresh "x" in fintro_ident x
      | [ |- ?A ⊢ (?s --> ?t) ] => apply II
      | [ |- ?A ⊩ (?s --> ?t) ] => apply II
      (* Special care for intro in proof mode *)
      | [ |- @pm _ _ ?p ?C (named_quant All _ ?t) ] => let x := fresh "x" in fintro_ident x
      | [ |- @tpm _ _ ?p ?C (named_quant All _ ?t) ] => let x := fresh "x" in fintro_ident x
      | [ |- @pm _ _ ?p ?C (?s --> ?t) ] => apply II; let name := name_from_pattern C id in change (@pm _ _ p (ccons name s C) t)
      | [ |- @tpm _ _ ?p ?C (?s --> ?t) ] => apply II; let name := name_from_pattern C id in change (@tpm _ _ p (tcons name s C) t)
      | _ =>
        (* Unfold definitions to check if there are hidden ∀ underneath. 
         * Also perform simplification and fix names if the definition
         * does something nasty. *)
        progress custom_unfold; simpl_subst; try update_binder_names;
        custom_unfold; (* Unfold again because [simpl_subst] folds *)
        fintro_pat' pat;
        custom_fold
      end
  end.

Ltac fintro_pat intro_pat := 
  match eval cbn in (parse_intro_pattern intro_pat) with
  | Some ?p => fintro_pat' p
  | None => let msg := eval cbn in ("Invalid intro pattern: " ++ intro_pat) in fail 2 msg
  end.

Tactic Notation "fintro" := fintro_pat constr:("?").
Tactic Notation "fintro" constr(H) := fintro_pat H.
Tactic Notation "fintro" ident(x) := fintro_ident x.

Tactic Notation "fintros" := repeat fintro.

Tactic Notation "fintros" constr(H1) := fintro_pat H1.
Tactic Notation "fintros" ident(H1) := fintro_ident H1.

Tactic Notation "fintros" constr(H1) constr(H2) := fintro_pat H1; fintro_pat H2.
Tactic Notation "fintros" ident(H1) constr(H2) := fintro_ident H1; fintro_pat H2.
Tactic Notation "fintros" constr(H1) ident(H2) := fintro_pat H1; fintro_ident H2.
Tactic Notation "fintros" ident(H1) ident(H2) := fintro_ident H1; fintro_ident H2.

Tactic Notation "fintros" constr(H1) constr(H2) constr(H3) := fintro_pat H1; fintro_pat H2; fintro_pat H3.
Tactic Notation "fintros" ident(H1) constr(H2) constr(H3) := fintro_ident H1; fintro_pat H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) ident(H2) constr(H3) := fintro_pat H1; fintro_ident H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) constr(H2) ident(H3) := fintro_pat H1; fintro_pat H2; fintro_ident H3.
Tactic Notation "fintros" ident(H1) ident(H2) constr(H3) := fintro_ident H1; fintro_ident H2; fintro_pat H3.
Tactic Notation "fintros" constr(H1) ident(H2) ident(H3) := fintro_pat H1; fintro_ident H2; fintro_ident H3.
Tactic Notation "fintros" ident(H1) ident(H2) ident(H3) := fintro_ident H1; fintro_ident H2; fintro_ident H3.





(* 
 * [fspecialize (H x1 x2 ... xn)], [fspecialize H with x1 x2 ... xn] 
 * 
 * Specializes a Coq hypothesis `H` of the form `X ⊢ ∀∀...∀ p1 --> ... --> pn --> g`
 * with `x1, x2, ..., xn`.
 *)

Ltac fspecialize_list H A := 
  match A with
  | [] => simpl_subst H
  | ?x::?A' =>
      tryif apply (fun H => IE _ _ _ H x) in H
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

Section Fapply.
  Context {Σ_funcs : funcs_signature}.  
  Context {Σ_preds : preds_signature}.
  Variable p : peirce.

  Lemma fapply_equiv_l A phi psi :
    A ⊢ (phi <--> psi) -> A ⊢ phi -> A ⊢ psi.
  Proof.
    intros. apply (IE _ phi). eapply CE1. apply H. apply H0.
  Qed.

  Lemma fapply_equiv_r A phi psi :
    A ⊢ (phi <--> psi) -> A ⊢ psi -> A ⊢ phi.
  Proof.
    intros. apply (IE _ psi). eapply CE2. apply H. apply H0.
  Qed.

  Lemma fapply_equiv_l_T A phi psi :
    A ⊩ (phi <--> psi) -> A ⊩ phi -> A ⊩ psi.
  Proof.
    intros. apply (IE _ phi). eapply CE1. apply H. apply H0.
  Qed.

  Lemma fapply_equiv_r_T A phi psi :
    A ⊩ (phi <--> psi) -> A ⊩ psi -> A ⊩ phi.
  Proof.
    intros. apply (IE _ psi). eapply CE2. apply H. apply H0.
  Qed.
End Fapply.

(* Helper tactics: *)

(* [fapply_without_quant] takes a formula `H : X ⊢ p1 --> p2 --> ... --> pn --> g`
 * without leading quantifiers. It solves the goal `X ⊢ g` by adding subgoals for
 * each premise `p1, p2, ..., pn`.
 * Also supports formulas of Type `H : X ⊢ ... --> (pn <--> g)` or 
 * `H : X ⊢ ... --> (g <--> pn)`.
 * If ∀-quantifiers occur inbetween, they are instantiated with evars. *)
Ltac fapply_without_quant H :=
  tryif exact H then idtac else
  let Hs := fresh "Hs" in 
  let Ht := fresh "Ht" in 
  match get_form_hyp H with
  | ?s --> ?t => 
    match goal with 
    | [ |- @prv _ _ ?p ?A _ ] =>
        enough (@prv _ _ p A s) as Hs; 
        [ assert (@prv _ _ p A t) as Ht; 
          [ apply (IE _ _ _ H Hs) | fapply_without_quant Ht; clear Hs; clear Ht ] 
        | ]
    | [ |- @tprv _ _ ?p ?A _ ] =>
        enough (@tprv _ _ p A s) as Hs; 
        [ assert (@tprv _ _ p A t) as Ht; 
          [ apply (IE _ _ _ H Hs) | fapply_without_quant Ht; clear Hs; clear Ht ] 
        | ]
    end
  
  (* Handle application of equivalence. It would be nice to use match
   * to check which side matches, but it doesn't work because of evars.
   * Therefore simply try both options. *)
  | _ <--> _ =>
    match goal with
    | [ |- _ ⊢ _] => tryif apply (fapply_equiv_l _ _ _ _ H) then idtac else apply (fapply_equiv_r _ _ _ _ H)
    | [ |- _ ⊩ _] => tryif apply (fapply_equiv_l_T _ _ _ _ H) then idtac else apply (fapply_equiv_r_T _ _ _ _ H)
    end
  
  (* Quantifiers are instantiated with evars *)
  | ∀ _ => eapply AllE in H; simpl_subst H; fapply_without_quant H

  (* If we don't find something useful, try unfolding definitions to 
   * check if there is something hidden underneath. Also perform 
   * simplification and fix names if the definition does something 
   * nasty. *)
  | _ =>
    match type of H with ?r => idtac r end;
    progress custom_unfold; simpl_subst H;
    custom_unfold; (* Unfold again because [simpl_subst] folds *)
    fapply_without_quant H;
    custom_fold
  end.

Ltac instantiate_evars H := repeat eassert (H := H _); repeat eapply AllE in H.
(* Tactic Notation "is_hyp" hyp(H) := idtac. *)
Ltac is_hyp H := match type of H with ?t => match type of t with Prop => idtac end end.

(* Check wether T is a hypothesis, a context index, a context formula
 * or a context name and put it into hypothesis H. *)
Ltac turn_into_hypothesis T H contxt := 
  tryif is_hyp T
  then assert (H := T)  (* Hypothesis *)
  else match goal with 
  | [ |- @prv _ _ ?p ?C _ ] => 
      match type of T with
      | form => assert (@prv _ _ p C T) as H by ctx  (* Explicit form *)
      | nat => let T' := nth C T in assert (@prv _ _ p C T') as H by ctx  (* Idx in context *)
      | string => match lookup contxt T with  (* Context name *)
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
        | @Some _ ?n => let T' := nth C n in assert (@prv _ _ p C T') as H by ctx
        end
      end
  | [ |- @tprv _ _ ?p ?C _ ] => 
      match type of T with
      | form => assert (@tprv _ _ p C T) as H by ctx  (* Explicit form *)
      | nat => let T' := nth C T in assert (@tprv _ _ p C T') as H by ctx  (* Idx in context *)
      | string => match lookup contxt T with  (* Context name *)
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 4 msg
        | @Some _ ?n => let T' := nth C n in assert (@tprv _ _ p C T') as H by ctx
        end
      end
  end.

(* If `H` has the type `P1 -> P2 -> ... -> Pn -> (A ⊢ ϕ)`, this
 * tactic adds goals for `P1, P2, ..., Pn` and specializes `H`. *)
Ltac assert_premises H :=
  match type of H with
  | ?A -> ?B => 
      let H' := fresh "H" in assert A as H';
      [|specialize (H H'); clear H'; assert_premises H ]
  | forall _, _ => eassert (H := H _); assert_premises H
  | _ => idtac
  end.

Ltac feapply' T A := fun contxt =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` contains further Coq premises before the formula 
   * statement, we add them as additional goals. *)
  assert_premises H;
  (* Only try here, because it would fail on these additional goals. *)
  try (
    fspecialize_list H A;
    instantiate_evars H;
    simpl_subst H;
    let C := get_context_goal in 
    eapply (Weak _ C) in H; [| firstorder];
    fapply_without_quant H; 
    (* [fapply_without_quant] creates the subgoals in the wrong order.
     * Reverse them to to get the right order: *)
    revgoals
  );
  clear H.

Ltac fapply' T A contxt :=
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  (* If `H` containe further Coq premises before the formula 
   * statement, we add them as additional goals. *)
  assert_premises H;
  (* Only try here, because it would fail on these additional goals. *)
  try (
    fspecialize_list H A; 
    instantiate_evars H; 
    simpl_subst H;
    let C := get_context_goal in
    eapply (Weak _ C) in H; [| firstorder];
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
  );
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

Section Fassert.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma fassert_help `{peirce} A phi psi :
    A ⊢ phi -> A ⊢ (phi --> psi) -> A ⊢ psi.
  Proof.
    intros H1 H2. eapply IE. exact H2. exact H1.
  Qed.

  Lemma fassert_help_T `{peirce} A phi psi :
    A ⊩ phi -> A ⊩ (phi --> psi) -> A ⊩ psi.
  Proof.
    intros H1 H2. eapply IE. exact H2. exact H1.
  Qed.
End Fassert.

Ltac fassert' phi := fun _ =>
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  match goal with
  | [ |- ?A ⊢ ?psi ] =>
    assert (A ⊢ phi) as H1; [ | 
      assert (A ⊢ (phi --> psi)); [ clear H1 |
        apply (fassert_help A phi psi H1 H2)
      ]
    ]
  | [ |- ?A ⊩ ?psi ] =>
    assert (A ⊩ phi) as H1; [ | 
      assert (A ⊩ (phi --> psi)); [ clear H1 |
        apply (fassert_help_T A phi psi H1 H2)
      ]
    ]
  end.

Tactic Notation "fassert" constr(phi) := (make_compatible ltac:(fassert' phi)); [| fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) := (make_compatible ltac:(fassert' phi)); [| fintro_pat H].
Tactic Notation "fassert" constr(phi) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro].
Tactic Notation "fassert" constr(phi) "as" constr(H) "by" tactic(tac) := (make_compatible ltac:(fassert' phi)); [tac | fintro_pat H].





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
    | [ |- prv _ _ ] => apply -> switch_imp; fintro_pat' pat
    | [ |- tprv _ _ ] => apply -> switch_imp_T; fintro_pat' pat
    | [ |- pm (ccons _ ?t ?C) ?phi ] => apply -> switch_imp; change (pm C (t --> phi)); fintro_pat' pat
    | [ |- tpm (tcons _ ?t ?C) ?phi ] => apply -> switch_imp_T; change (tpm C (t --> phi)); fintro_pat' pat
    end
  | S ?n' =>
    match goal with 
    | [ |- prv _ _ ] => apply -> switch_imp; fdestruct' n' pat; apply <- switch_imp
    | [ |- tprv _ _ ] => apply -> switch_imp_T; fdestruct' n' pat; apply <- switch_imp_T
    | [ |- pm  (ccons ?a ?t ?C) ?phi ] => 
        apply -> switch_imp; change (pm C (t --> phi)); fdestruct' n' pat;
        match goal with [ |- pm ?C' (t --> phi) ] => 
          apply <- switch_imp; change (pm (ccons a t C') phi)
        end
    | [ |- tpm (tcons ?a ?t ?C) ?phi ] => 
        apply -> switch_imp_T; change (tpm C (t --> phi)); fdestruct' n' pat;
        match goal with [ |- tpm ?C' (t --> phi) ] => 
          apply <- switch_imp_T; change (tpm (tcons a t C') phi)
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
    let s := get_form_hyp H in
    match goal with
    | [ |- prv ?A ?t ] => enough (A ⊢ (s --> t)) as X by (feapply X; feapply H)
    | [ |- tprv ?A ?t ] => enough (A ⊩ (s --> t)) as X by (feapply X; feapply H)
    | [ |- pm ?A ?t ] => enough (pm A (s --> t)) as X by (feapply X; feapply H)
    | [ |- tpm ?A ?t ] => enough (tpm A (s --> t)) as X by (feapply X; feapply H)
    end;
    fintro "?"; fdestruct'' 0 pat; clear H
  )
  else (
    let n := match type of T with 
      | nat => T 
      | string =>
        let C := get_context_goal in
        match lookup C T with 
        | @Some _ ?n' => n'
        | @None => let msg := eval cbn in ("Unknown identifier: " ++ T) in fail 3 msg
        end
      end
    in
    let pattern := lazymatch pat with
      | "" => let C := get_context_goal in let t := nth C n in create_pattern t
      | _ => 
        match eval cbn in (parse_intro_pattern pat) with 
        | @Some _ ?p => p
        | @None => let msg := eval cbn in ("Invalid pattern: " ++ pat) in fail 3 msg
        end
    end in fdestruct' n pattern
  ).

Tactic Notation "fdestruct" constr(T) := fdestruct'' T "".
Tactic Notation "fdestruct" constr(T) "as" constr(pat) := fdestruct'' T pat.






(** Classical Logic *)

Section Classical.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Lemma case_help A phi psi :
    A ⊢C (phi ∨ (phi --> ⊥) --> psi) -> A ⊢C psi.
  Proof.
    intro H. eapply IE. apply H.
    eapply IE. eapply Pc.
    apply II. apply DI2. apply II.
    eapply IE. apply Ctx. right. now left.
    apply DI1. apply Ctx. now left.
  Qed.

  Lemma case_help_T A phi psi :
    A ⊩C (phi ∨ (phi --> ⊥) --> psi) -> A ⊩C psi.
  Proof.
    intro H. eapply IE. apply H.
    eapply IE. eapply Pc.
    apply II. apply DI2. apply II.
    eapply IE. apply Ctx. firstorder.
    apply DI1. apply Ctx. firstorder.
  Qed.

  Lemma contradiction_help A phi :
    A ⊢C ((phi --> ⊥) --> ⊥) -> A ⊢C phi.
  Proof.
    intro H. eapply IE. eapply Pc. apply II.
    apply Exp. eapply IE. eapply Weak. apply H. firstorder.
    apply II. eapply IE. apply Ctx. right. now left.
    apply Ctx. now left.
  Qed.

  Lemma contradiction_help_T A phi :
    A ⊩C ((phi --> ⊥) --> ⊥) -> A ⊩C phi.
  Proof.
    intro H. eapply IE. eapply Pc. apply II.
    apply Exp. eapply IE. eapply Weak. apply H. firstorder.
    apply II. eapply IE. apply Ctx. firstorder.
    apply Ctx. firstorder.
  Qed.

End Classical.


Tactic Notation "fclassical" constr(phi) "as" constr(H1) constr(H2) := 
  make_compatible ltac:(fun _ => 
    match goal with
    | [ |- _ ⊢ _ ] => apply (case_help _ phi)
    | [ |- _ ⊩ _ ] => apply (case_help_T _ phi)
    end
  ); let pat := eval cbn in ("[" ++ H1 ++ "|" ++ H2 ++ "]") in fintro_pat pat.
Tactic Notation "fclassical" constr(phi) "as" constr(H) := fclassical phi as H H.
Tactic Notation "fclassical" constr(phi) := fclassical phi as "".

Tactic Notation "fcontradict" "as" constr(H) := 
  make_compatible ltac:(fun _ => 
    match goal with 
    | [ |- _ ⊢ _ ] => apply contradiction_help
    | [ |- _ ⊩ _ ] => apply contradiction_help_T
    end
  ); fintro_pat H.
Tactic Notation "fcontradict" := fcontradict as "?".








Definition cast {X} {x y: X} {p: X -> Type}
  : x = y -> p x -> p y
  := fun e a => match e with eq_refl => a end.

Class Leibniz (Σ_funcs : funcs_signature) (Σ_preds : preds_signature) :=
{
  Eq_pred : preds ;
  eq_binary : 2 = ar_preds Eq_pred ;
  (* eq s t := @atom Σ_funcs Σ_preds _ Eq (@eq_rect _ _ (fun n : nat => Vector.t term n) (Vector.cons term s 1 (Vector.cons term t 0 (Vector.nil term))) _ eq_binary) ; *)
  eq s t := @atom Σ_funcs Σ_preds _ Eq_pred (cast eq_binary (Vector.cons term s 1 (Vector.cons term t 0 (Vector.nil term)))) ;

  Axioms : list form ;
  Axioms_T : theory ;
  (* Axioms_T_closed : closed_theory Axioms_T ; *)
  (* sym `{peirce} : Axioms ⊢ ∀ ∀ (eq ($0) ($1) --> eq ($1) ($0)) ; *)
  sym_T `{peirce} T : Axioms ⊏ T ->  T ⊩ ∀ ∀ (eq ($0) ($1) --> eq ($1) ($0)) ;
  leibniz `{peirce} A phi t t' : Axioms <<= A -> A ⊢ eq t t' -> A ⊢ phi[t..] -> A ⊢ phi[t'..] ;
  leibniz_T `{peirce} T phi t t' : Axioms_T ⊑ T -> T ⊩ eq t t' -> T ⊩ phi[t..] -> T ⊩ phi[t'..]
}.


Lemma eq_subst_help `{funcs_signature} f y t1 t2 (e : 2 = y) :
  Vector.map f (cast e (Vector.cons term t1 1 (Vector.cons term t2 0 (Vector.nil term)))) = cast e (@Vector.map term term f _ (Vector.cons term t1 1 (Vector.cons term t2 0 (Vector.nil term)))).
Proof.
  destruct e. reflexivity.
Qed.

Lemma eq_subst `{L : Leibniz} t1 t2 s :
  (eq t1 t2)[s] = eq (t1`[s]) (t2`[s]).
Proof.
  cbn. rewrite eq_subst_help. cbn. reflexivity.
Qed.

Lemma sym `{Leibniz, peirce} :
  Axioms ⊢ ∀ ∀ (eq $0 $1 --> eq $1 $0).
Proof.
  intros. fintros s t. repeat (rewrite eq_subst_help; cbn).
  change (Axioms ⊢ (eq t s`[↑]`[t..] --> eq s`[↑]`[t..] t)). simpl_subst.
  fintro. enough ((eq t s :: Axioms) ⊢ (eq t s --> eq s t)). eapply IE. apply H1. ctx.
  enough ((eq t s::Axioms) ⊢ (eq t`[↑]`[s..] $0`[s..] --> eq $0`[s..] t`[↑]`[s..])) as X by now rewrite subst_term_shift in X.
  enough ((eq t s::Axioms) ⊢ (eq t`[↑] $0 --> eq $0 t`[↑])[s..]) by now rewrite <- ! eq_subst.
  eapply leibniz. firstorder. apply Ctx. now left. cbn. repeat (rewrite eq_subst_help; cbn).
  change ((eq t s :: Axioms) ⊢ (eq t`[↑]`[t..] t --> eq t t`[↑]`[t..])).
  rewrite subst_term_shift.
  apply II. apply Ctx. now left.
Qed.

(* Lemma sym_T `{peirce, Leibniz} :
  Axioms_T ⊩ ∀ ∀ (eq ($0) ($1) --> eq ($1) ($0)).
Proof.
  apply AllI, AllI.
  pose (T' := mapT (subst_form ↑) (mapT (subst_form ↑) Axioms_T)).
  pose (t := $0). pose (s := $1).
  fintro. enough ((T' ⋄ eq t s) ⊩ (eq t s --> eq s t)) as X. eapply IE. apply X.
  apply Ctx. now right.
  enough ((T' ⋄ eq t s) ⊩ (eq t`[↑]`[s..] $0`[s..] --> eq $0`[s..] t`[↑]`[s..])) as X by now rewrite subst_term_shift in X.
  enough ((T' ⋄ eq t s) ⊩ (eq t`[↑] $0 --> eq $0 t`[↑])[s..]) by now rewrite <- ! eq_subst.
  eapply leibniz_T.
  { intros phi H2. left. exists phi. split. exists phi. split. now apply H2.
    all: apply subst_closed; now apply Axioms_T_closed. }
  apply Ctx. now right.
  cbn. repeat (rewrite eq_subst_help; cbn).
  change ((T' ⋄ eq t s) ⊩ (eq t t --> eq t t)).
  apply II. ctx.
Qed. *)

Fixpoint up_n `{funcs_signature} n sigma := match n with
| 0 => sigma
| S n' => up (up_n n' sigma)
end.

Ltac shift_n n t := 
  match n with
  | 0 => t
  | S ?n' => shift_n n' (t`[↑])
  end.

Ltac vector_map_ltac v f :=
  match v with
  | Vector.nil ?t => constr:(Vector.nil t)
  | @Vector.cons _ ?x _ ?v' =>
    let x' := f x in 
    let v'' := vector_map_ltac v' f in
    constr:(@Vector.cons _ x' _ v'')
  end.

(* Returns a new formula where all occurences of `t` are turned into
 * `($n)[up_n n t..]` and every other term `s` into `s[up_n n ↑][up_n t..]`,
 * where `n` is the quantor depth. *)
Ltac add_shifts' n t G :=
  let f := add_shifts' n t in 
  let t_shifted := shift_n n t in
  match G with
  (* Terms: *)
  | t_shifted => constr:(($n)`[up_n n t..])
  | $(?m) => constr:(($m)`[up_n n ↑]`[up_n n t..])
  | func ?fu ?vec => let vec' := vector_map_ltac vec f in constr:(func fu vec')
  (* Formulas: *)
  | fal => constr:(fal[up_n n ↑][up_n n t..])
  | atom ?P ?vec => let vec' := vector_map_ltac vec f in constr:(atom P vec')
  | bin ?op ?u ?v => let u' := f u in let v' := f v in constr:(bin op u' v')
  | quant ?op ?u => let u' := add_shifts' (S n) t u in constr:(quant op u')
  (* Fallback for variables which cannot be matched syntactically: *)
  | ?u => match type of u with 
      | form => constr:(u[up_n n ↑][up_n n t..])
      | term => constr:(u`[up_n n ↑]`[up_n n t..])
      end
  end.
Ltac add_shifts := add_shifts' 0.

(* Returns a new formula where all occurences of `s[up_n n ↑][up_n nt..]` 
 * in G are turned into `s[up_n n ↑]` and `($n)[up_n n t..]` into `$n`. *)
Ltac remove_shifts G t :=
  match G with 
  | context C[ ?s[up_n ?n ↑][up_n ?n t..] ] => let G' := context C[ s[up_n n ↑] ] in remove_shifts G' t
  | context C[ ?s`[up_n ?n ↑]`[up_n ?n t..] ] => let G' := context C[ s`[up_n n ↑] ] in remove_shifts G' t
  | context C[ ($ ?n)`[up_n ?n t..] ] => let G' := context C[ $n ] in remove_shifts G' t
  | _ => G
  end.

Ltac frewrite' T A back := fun contxt =>
  let H := fresh "H" in
  turn_into_hypothesis T H contxt;
  fspecialize_list H A; 
  instantiate_evars H; 
  simpl_subst H;

  (* For some reason the match below binds `_t` and `_t'` to terms
   * with unfolded constants (like `zero` in PA). This messes up
   * syntactic matching later. Therefore just unfold everything,
   * do the rewriting and fold back later. *)
  custom_unfold;

  match get_form_hyp H with atom ?p (@Vector.cons _ ?_t _ (@Vector.cons _ ?_t' _ (Vector.nil term))) =>
    (* Make sure that we have equality *)
    assert (p = Eq_pred) as _ by reflexivity;

    let t := match back with true => _t' | false => _t end in
    let t' := match back with true => _t | false => _t' end in
    
    (* 1. Replace each occurence of `t` with `($n)[up_n n t..]` and every
     *  other `s` with `s[up_n n ↑][up_n n t..]`. The new formula is 
     *  created with the [add_shifts] tactic and proven in place. *)
    let C := get_context_goal in
    let G := get_form_goal in
    let X := fresh in
    let G' := add_shifts t G in
    match goal with
    | [ |- _ ⊢ _ ] => enough (C ⊢ G') as X
    | [ |- _ ⊩ _ ] => enough (C ⊩ G') as X
    end;
    [
      repeat match type of X with context K[ ?u`[up_n ?n ↑]`[up_n ?n t..] ] =>
        let R := fresh in
        (* TODO: Prove general lemma for this: *)
        assert (u`[up_n n ↑]`[up_n n t..] = u) as R; [
          rewrite subst_term_comp; apply subst_term_id; 
          let a := fresh in intros a;
          (do 10 try destruct a); reflexivity |];
        rewrite R in X
      end;
      apply X
    |];
    
    (* 2. Pull out the [t..] substitution *)
    match goal with 
    | [ |- ?U ⊢ ?G ] => let G' := remove_shifts G t in change (U ⊢ G'[t..])
    | [ |- ?U ⊩ ?G ] => let G' := remove_shifts G t in change (U ⊩ G'[t..])
    end;
    
    (* 3. Change [t..] to [t'..] using leibniz. For some reason
     *  we cannot directly [apply leibniz with (t := t')] if t'
     *  contains ⊕, σ, etc. But evar seems to work. *)
    let t'' := fresh "t" in 
    match goal with
    | [ |- _ ⊢ _ ] => eapply (leibniz _ _ ?[t''])
    | [ |- _ ⊩ _ ] => eapply (leibniz_T _ _ ?[t''])
    end;
    [ instantiate (t'' := t'); firstorder |
      match back with
      | false => let H_sym := fresh in assert (H_sym := sym); feapply H_sym; clear H_sym; fapply H
      | true => apply H
      end
    | ];
    
    (* 4. Pull substitutions inward, but don't unfold `up_n` *)
    cbn -[up_n];
    
    (* 5. Turn subst_term calls back into []-Notation *)
    (* repeat match goal with [ |- context C`[subst_term ?sigma ?s] ] =>
      let G' := context C[ s`[sigma] ] in change G'
    end; *)

    (* 6. Fix simplification that occurs because of cbn *)
    repeat match goal with [ |- context C[up_n ?n ↑ ?a] ] =>
      let G' := context C[ ($a)[up_n n ↑] ] in change G'
    end;

    (* 7. Change `up (up ...)` back into `up_n n ...` *)
    repeat match goal with 
    | [ |- context C[up_n ?n (up ?s)]] => let G' := context C[up_n (S n) s] in change G'
    | [ |- context C[up ?s]] => let G' := context C[up_n 1 s] in change G'
    end;
    
    (* 8. Simplify *)
    repeat match goal with [ |- context K[ ?u `[up_n ?n ↑]`[up_n ?n t'..] ]] =>
      let R := fresh in
      (* TODO: Prove general lemma for this: *)
      assert (u`[up_n n ↑]`[up_n n t'..] = u) as R; [
        rewrite subst_term_comp; apply subst_term_id; 
        let a := fresh in intros a;
        (do 10 try destruct a); reflexivity |];
      rewrite ! R;
      clear R
    end;

    (* Base case for rewrite without quantors *)
    cbn; try rewrite !subst_shift; try rewrite !subst_term_shift;

    (* Final simplifications *)
    custom_fold;
    simpl_subst
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




Ltac fexists x := make_compatible ltac:(fun _ => 
  apply ExI with (t := x); 
  simpl_subst).


(* Section Test.

Require Import ZF.

Variable p : peirce.

Definition ax_refl := ∀ $0 ≡ $0.
Definition ax_sym := ∀ ∀ $1 ≡ $0 --> $0 ≡ $1.
Definition ax_trans := ∀ ∀ ∀ $2 ≡ $1 --> $1 ≡ $0 --> $2 ≡ $0.
Definition ax_eq_elem := ∀ ∀ ∀ ∀ $3 ≡ $1 --> $2 ≡ $0 --> $3 ∈ $2 --> $1 ∈ $0.

Definition ZF := ax_ext::ax_eset::ax_pair::ax_union::ax_power::ax_om1::ax_om2::ax_refl::ax_sym::ax_trans::ax_eq_elem::nil.


Ltac custom_fold ::= fold sub in *.
Ltac custom_unfold ::= unfold sub in *.

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
Admitted.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊢ (x ≡ x' --> y ≡ y'--> {x; y} ≡ {x'; y'}).
Proof.
  fstart. fintros "H1" "H2". fapply ax_ext. fintros z.
  - fapply ZF_sub_pair'.
Qed.

End Test. *)




(* Section Test.

Require Import PA.

Variable p : peirce.

Ltac custom_fold ::= fold zero in *.
Ltac custom_unfold ::= unfold zero in *.
Ltac custom_simpl ::= try rewrite !numeral_subst_invariance.

Program Instance PA_Leibniz : Leibniz PA_funcs_signature PA_preds_signature.
Next Obligation. exact Eq. Defined.
Next Obligation. exact FA. Defined.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.


End Test. *)
