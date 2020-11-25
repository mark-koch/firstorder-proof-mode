Require Import FOL.
Require Import Tarski.
Require Import PA.
Require Import Vector.


Inductive bterm `{funcs_signature} :=
| bVar : nat -> bterm
| bFunc : forall (f : syms), vec bterm (ar_syms f) -> bterm
| bEmbedT : term -> bterm.

Inductive bform `{funcs_signature, preds_signature, operators} :=
  | bFal : bform
  | bAtom : forall (P : preds), vec bterm (ar_preds P) -> bform
  | bBin : binop -> bform  -> bform  -> bform
  | bQuant : quantop -> (bterm -> bform)  -> bform
  | bFree : (bterm -> bform)  -> bform.

Fixpoint conv_term `{funcs_signature} i (b : bterm) : term :=
  match b with
  | bVar m => var (i - m)
  | bEmbedT t => t
  | bFunc f v => func f (Vector.map (conv_term i) v)
  end.

Fixpoint conv `{funcs_signature, preds_signature, operators} i (phi : bform) : form :=
  match phi with
  | bFal => fal
  | bAtom p v => atom p (Vector.map (conv_term i) v)
  | bBin op t1 t2 => bin op (conv i t1) (conv i t2)
  | bQuant op f => quant op (conv (S i) (f (bVar (S i))))
  | bFree f => conv (S i) (f (bVar (S i)))
  end.

Declare Scope hoas_scope.
Delimit Scope hoas_scope with hoas.

Notation "'Free' x .. y , p" := (bFree Ex (fun x => .. (bFree Ex (fun y => p)) ..))
(at level 50, x binder, left associativity,
  format "'[' 'Free'  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "'∀' x .. y , p" := (bQuant All (fun x => .. (bQuant All (fun y => p)) ..))
(at level 50, x binder, left associativity,
  format "'[' '∀'  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "'∃' x .. y , p" := (bQuant Ex (fun x => .. (bQuant Ex (fun y => p)) ..))
(at level 50, x binder, left associativity,
  format "'[' '∃'  '/  ' x  ..  y ,  '/  ' p ']'") : hoas_scope.
Notation "⊥" := (bFal) : hoas_scope.
Notation "A ∧ B" := (bBin Conj A B) (at level 41) : hoas_scope.
Notation "A ∨ B" := (bBin Disj A B) (at level 42) : hoas_scope.
Notation "A '-->' B" := (bBin Impl A B) (at level 43, right associativity) : hoas_scope.

Notation "'σ' x" := (@bFunc PA_funcs_signature Succ (Vector.cons x (Vector.nil bterm))) (at level 37) : hoas_scope.
Notation "x '⊕' y" := (@bFunc PA_funcs_signature Plus (Vector.cons x (Vector.cons y (Vector.nil bterm))) ) (at level 39) : hoas_scope.
Notation "x '⊗' y" := (@bFunc PA_funcs_signature Mult (Vector.cons x (Vector.cons y (Vector.nil bterm))) ) (at level 38) : hoas_scope. 
Notation "x '==' y" := (@bAtom PA_funcs_signature PA_preds_signature _ Eq (Vector.cons bterm x 1 (Vector.cons bterm y 0 (Vector.nil bterm))) ) (at level 40) : hoas_scope.

Definition convert `{funcs_signature, preds_signature, operators} f := (@conv _ _ _ 0 f).
Arguments convert {_ _ _} f%hoas.

Notation "<< f" := (ltac:(let y := eval cbn -[subst_form] in (convert f) in exact y)) (at level 200, only parsing).


(* 
Section Test.
  Require Import Deduction.
  Require Import List.

  Variable p : peirce.

  (* TODO: Why ist the `%hoas` needed? *)
  Goal nil ⊢ << (∀ a, a == a)%hoas.
  Abort.

End Test. 
*)
