Require Import FOL.
Require Import Equations.Equations Equations.Prop.DepElim.
Require Import Lia.
Require Import Vector.

Section Vectors.


  (* function that does the conjuction over all entries of a Boolean vector *)
  Fixpoint andb_vec {n} (v : t bool n) :=
    match v with
    | nil _ => true
    | cons _ b n w => andb b (andb_vec w)
    end.



  Fixpoint max_vec {n} (v : t nat n ) :=
    match v with
    | nil _ => 0
    | cons _ k n w => PeanoNat.Nat.max k (max_vec w)
    end.



  Lemma help {X N} x a (v : t X N) :
    In x (cons _ a _ v) -> x = a \/ In x v.
  Proof.
    intros H. inversion H;subst.
    eapply EqDec.inj_right_pair in H3; subst.
    - now left.
    - eapply EqDec.inj_right_pair in H3; subst. now right.
  Qed.


  Lemma vec_true_entries {N} v :
    andb_vec v = true -> forall b, @In _ b N v -> b = true.
  Proof.
    induction v.
    - intros _ b H. inversion H.
    - cbn. intros []%andb_prop b Hin.
      apply help in Hin as [<-|].
      assumption. now apply IHv.
  Qed.



  Lemma vec_max_entries {N} v :
    forall B, max_vec v <= B -> forall n : nat, @In _ n N v -> n <= B.
  Proof.
    induction v.
    - intros B _ n H. inversion H.
    - cbn. intros B H m Hin.
      apply help in Hin as [<-|]. 
      now apply PeanoNat.Nat.max_lub_l in H.
      apply IHv. now apply PeanoNat.Nat.max_lub_r in H. auto.
  Qed.


  (* produces a vector where the order of the values is fliped; *)
  (* the 0-th entry of the vector is (sigma N) and the N-th is (sigma 0) *)
  Fixpoint first_of {X} N (sigma : nat -> X) : t X (S N) :=
    match N with
    | O => cons _ (sigma 0) 0 (nil _)
    | S n => cons _ (sigma N) _ (first_of n sigma)
    end.


  (* first_of flips the order of the elements we take away. So when we join 
     it again with the rest of the environment, we need to do another flip 
     during the joining. *)
  Fixpoint join {X n} (v : t X n) (rho : nat -> X) :=
    match v with
    | nil _ => rho
    | cons _ x n w  => join w (x.:rho)
    end.

  Notation "v '∗' rho" := (join v rho) (at level 20).

  (* now we define the fitting remaining part which we want to join *)
  Definition rest_of {X} (N : nat) (sigma : nat -> X) := fun x => sigma (x + S N).


  Lemma shift_rest_of {X : Type} N k (sigma : nat -> X) x :
    rest_of (N + k) sigma x = rest_of N sigma (x + k).
  Proof.
    unfold rest_of. f_equal. rewrite <- plus_Sn_m.
    pattern (S N + k). rewrite <- PeanoNat.Nat.add_comm.
    now rewrite PeanoNat.Nat.add_assoc.
  Qed.




  Lemma vec_hdtl_eq {X n} (v : t X (S n)) :
    v = Vector.cons X (hd v) n (tl v).
  Proof.
    pattern v. revert v; revert n. apply caseS. now cbn.
  Qed.


  Lemma vec_Onil_eq {X} (v : t X 0) : v = nil X.
  Proof.
    now refine (case0 (fun x => x = nil X) _ v ).
  Qed.


  Lemma vec_map_In {X Y N} (f : X -> Y) x (v : t X N) :
    In x v -> In (f x) (map f v).
  Proof.
    intros H. induction H; cbn; now constructor. 
  Qed.



  Lemma vec_join_after_N' {X N} (v : t X N ) :
    forall rho sigma k, (forall x, rho x = sigma x) -> (v ∗ rho) (N + k) = sigma k.
  Proof.
    induction N. rewrite (vec_Onil_eq _). now cbn.
    rewrite (vec_hdtl_eq _). intros rho sigma k Hext. cbn.
    rewrite <- PeanoNat.Nat.add_succ_r.
    change ( (tl v ∗ (hd v .: rho)) (N + S k)
             = (fun x => match x with
                      | S y => sigma y
                      | _ => hd v end) (S k) ).
    apply IHN. destruct x. now cbn. now rewrite <- Hext.
  Qed.



  Corollary vec_join_after_N {X N} (v : t X N ) :
    forall rho k, (v ∗ rho) (N + k) = rho k.
  Proof.
    intros rho k. now apply vec_join_after_N'.
  Qed.



  Lemma vec_join_at_N {X N} (v : t X N ) : forall rho, (v ∗ rho) N = rho 0.
  Proof.
    intros rho. change ((v ∗ rho) (0 + N) = rho 0).
    rewrite PeanoNat.Nat.add_comm. now refine (vec_join_after_N _ _ _).
  Qed.



  Lemma vec_join_ext {X N} (v : t X (S N) ) : forall rho sigma,
      forall n, n <= N -> (v ∗ rho) n = (v ∗ sigma) n.
  Proof.
    revert v. induction N.
    - intros v rho sigma n HN.
      enough (n = 0) as ->.
      rewrite (vec_hdtl_eq v). rewrite (vec_Onil_eq _).
      all : now intuition.
    - intros V rho sigma n HN. rewrite (vec_hdtl_eq _).
      remember (tl V) as v; cbn.
      enough (n = S N \/ n <= N) as [-> |].
      now rewrite !vec_join_at_N. now apply (IHN v _ _).
      lia.
  Qed.



  Lemma vec_join_before_N' {X N} :
    forall (sigma rho : nat -> X) k, k <= N -> (first_of N sigma ∗ rho) k = sigma k.
  Proof.
    induction N; intros sigma rho k Hk. enough (k = 0) as ->. now cbn. lia.
    enough (k = S N \/ k <= N) as [-> |]; cbn.
    apply vec_join_at_N. now apply IHN. lia.
  Qed.


  Lemma vec_join_before_N {X N} :
    forall (rho : nat -> X) k, k <= N -> (first_of N rho ∗ rho) k = rho k.
  Proof.
    intros. now apply vec_join_before_N'.
  Qed.


End Vectors.
