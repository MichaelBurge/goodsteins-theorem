Require Import Coq.Init.Peano.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Arith.
Require Import Bool.

Module Type RepresentationSig.
Parameter A : Type.
Parameter repr : nat -> nat -> A.
Parameter eval : A -> nat -> nat.

Axiom eq_eval_repr : forall n:nat, forall r:nat, eval (repr n r) r = n.
End RepresentationSig.

Inductive Polynomial : Type :=
  | poly_nil : Polynomial
  | poly_cons : nat -> Polynomial -> Polynomial.

Fixpoint poly_is_scale (poly:Polynomial) (scale:nat) : Prop :=
  match poly with
  | poly_nil => True
  | poly_cons n tail => n < scale /\ poly_is_scale tail scale
  end.

Fixpoint poly_dominating_power  (poly:Polynomial) : nat :=
  match poly with
  | poly_nil => 0
  | poly_cons n tail => 1 + poly_dominating_power tail
  end.

Fixpoint poly_succ (poly:Polynomial) (scale:nat) : Polynomial :=
  match poly with
  | poly_nil => poly_cons 1 poly_nil
  | poly_cons n tail =>
    if n + 1 <? scale
    then poly_cons (n+1) tail
    else poly_cons 0 (poly_succ tail scale)
  end.

 Fixpoint poly_repr (n:nat) (scale:nat) : Polynomial :=
   match n with 
   | 0 => poly_nil
   | S x => poly_succ (poly_repr x scale) scale
   end.

Fixpoint poly_eval (poly:Polynomial) (scale:nat) : nat :=
  match poly with
  | poly_nil => 0
  | poly_cons n tail => n + scale * (poly_eval tail scale)
  end.
Fixpoint poly_add (initial:Polynomial) (k:nat) (scale:nat) : Polynomial :=
  match k with 
  | 0 => initial
  | S x => poly_add (poly_succ initial scale) x scale
  end.

Definition poly_lift (n:nat) (scale:nat) : Polynomial :=
  poly_add poly_nil n scale.

Fixpoint poly_tail (poly:Polynomial) : Polynomial :=
  match poly with
  | poly_nil => poly_nil
  | poly_cons n tail => tail
  end.

Fixpoint poly_change (poly:Polynomial) (index:nat) (coefficient:nat) (scale:nat) : Polynomial :=
  match index with
  | 0 => poly_cons coefficient (poly_tail poly)
  | S x => poly_change poly x coefficient scale
  end.

Fixpoint poly_le (poly1 poly2 : Polynomial) : Prop :=
  match poly1 with
  | poly_nil => True
  | poly_cons n1 tail1 =>
    match poly2 with
    | poly_nil => False
    | poly_cons n2 tail2 =>
      n1 < n2 \/ (n1 = n2 /\ poly_le tail1 tail2)
    end
  end.

Functional Scheme poly_succ_ind := Induction for poly_succ Sort Prop.
Functional Scheme poly_repr_ind := Induction for poly_repr Sort Prop.
Functional Scheme poly_eval_ind := Induction for poly_eval Sort Prop.
Functional Scheme poly_add_ind := Induction for poly_add Sort Prop.
Functional Scheme poly_tail_ind := Induction for poly_tail Sort Prop.
Functional Scheme poly_change_ind := Induction for poly_change Sort Prop.
Functional Scheme poly_le_ind := Induction for poly_le Sort Prop.

Theorem nat_le_Sn :
  forall (n:nat),
    n < n+1.
Proof.
  admit.
  Qed.

Theorem poly_succ_le :
  forall (poly:Polynomial) (scale:nat),
    poly_le poly (poly_succ poly scale).
Proof.
  intros.
  functional induction poly_succ poly scale.

  (* Base case for poly_nil *)
  simpl.
  auto.

  (* Induction on n in poly_succ *)
  simpl.
  assert (n + 0 < n + 1).
  assert (0 < 1).
  auto.
  assert (n <= n+1).
  apply le_plus_l.
  apply plus_le_lt_compat with (n := n) (m := n) (p := 0) (q := 1).
  auto.
  auto.
  assert (n < n + 1).
  apply nat_le_Sn.  
  auto.

  (* Induction on poly_succ structurally *)
  induction n.
  simpl.
  apply or_intror.
  split.
  tauto.
  apply IHp.


  apply or_intror.
  apply 
  in auto.
  unfold poly_le.
  
  unfold plus.
  apply lt_n_Sn with (n := n).
Theorem poly_prop_succ :
  forall n scale : nat,
    poly_eval (poly_lift n scale) scale = n.
Proof.
  (* 1. Find the least index i with coef(i) + 1 < scale *)
  (* 2. Use scale^i = sum((scale - 1) * scale^j, j, 0, i) + 1 *)
  (* 3. *)
  induction.
  intros.
  unfold poly_lift.  
  functional induction poly_eval (poly scale.
  
 
Theorem poly_prop_repr_eval :
  forall n scale : nat,
  scale > 1 -> poly_eval (poly_repr n scale) scale = n.
Proof.
  intros.
  functional induction poly_repr n scale.
  simpl.
  auto.
  

  induction n.
  intros.  
  simpl.
  auto.
  intros.
  unfold poly_repr.
  unfold poly_eval.
  
Eval compute in poly_eval (poly_repr 43 3) 3.

 Inductive Skeleton : Type :=
   | Empty : Skeleton
   (* TermCons : coefficient -> exponent -> tail -> Skeleton *)
   | TermCons : nat -> Skeleton -> Skeleton -> Skeleton.

 Fixpoint is_of_scale (skeleton:Skeleton) (r:nat) : Prop :=
   match skeleton with
   | Empty => True
   | TermCons x exp tail => x < r /\ is_of_scale tail r
   end.

 Fixpoint degree (skeleton:Skeleton) : nat :=
   match skeleton with
   | Empty => 0
   | TermCons x exp tail => 1 + degree tail
   end.

 Fixpoint eval_skeleton (skeleton:Skeleton) (r:nat) : nat :=
   match skeleton with
   | Empty => 0
   | TermCons x exp tail => (eval_skeleton exp r) + r * (eval_skeleton tail r)
   end.

 (* n is decreasing with each recursive call, but not syntactically according to the definition of nat. 'counter' is used as an auxillary variable that does decrease syntactically - by destructuring 'S counter'. *)
 Fixpoint highest_power' (counter:nat) (n:nat) (r:nat) :=
   match counter with
   | S prev => 
     match r <=? n with
     | (true) =>
       let after_division := div n r
       in 1 + highest_power' prev after_division r
     | (false) => 0
     end
   | _ => 0
   end.


 Fixpoint highest_power (n:nat) (r:nat) : nat :=
   highest_power' n n r.


 Fixpoint repr_skeleton' (power:nat) (n:nat) (s:nat) : Skeleton :=
   match power with
   | S x =>
     let q := div n (s^power) in (
       let r := modulo n (s^power)
       in TermCons
            q
            (repr_skeleton' x power s)
            (repr_skeleton' x r s)
     )
   | 0 => TermCons n Empty Empty
   end.

 Fixpoint better_repr_skeleton (n:nat) (s:nat) : Skeleton :=
   if n < s
   then TermCons n Empty Empty
  else  
  match n with 
  | S n =>
    if n < s
    then 
  | 0 => TermCons 0 Empty Empty
  end.

Fixpoint repr_skeleton (n:nat) (s:nat) : Skeleton :=
  repr_skeleton' (highest_power n s) n s.

Eval compute in repr_skeleton 63 2.

Record Representation : Type := {
  skeleton : Skeleton;
  scale : nat;
  prop_repr_scale : is_of_scale skeleton scale
}.

Fixpoint max_degree (skeleton:Skeleton) : nat :=
  match skeleton with
  | Empty => 0
  | TermCons c exp tail => 1 + max_degree tail
  end.

Theorem strong_induction :
  forall P : nat -> Prop,
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n : nat, P n.
Proof.
  Admitted.

Check strong_induction.

Theorem skeleton_prop_eval_repr : forall (n r : nat), r > 1 -> eval_skeleton (repr_skeleton n r) r = n.
Proof.  
  induction n using strong_induction.
  intros.
  simpl.
  destruct (r <=? S n).
  simpl
  refine (strong_induction _ _).

  intros.
  apply strong_induction
  induction n using strong_induction.
  intros.
  intros.
  simpl.
  apply mult_0_r.
  intros.
  simpl.
  set (term := r <=? S n).
  assert ({term = true} + {term <> true}).
  apply bool_dec.
  destruct H0.
  set (term2 := if term then S (highest_power' n (S n / r) r) else 0).
  destruct term.
  simpl.
  
  assertterm \/ ~term). apply classic.