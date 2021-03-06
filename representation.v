Require Import Coq.Init.Peano.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Structures.Orders.
Require Import Arith.
Require Import Bool.
Require Import Classical.

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

 Fixpoint poly_eq (poly1 poly2 : Polynomial) : Prop :=
   match poly1 with
   | poly_nil => poly2 = poly_nil
   | poly_cons n1 tail1 =>
     match poly2 with
     | poly_nil => False
     | poly_cons n2 tail2 =>
       n1 = n2 /\ poly_eq tail1 tail2
     end
   end.

 Fixpoint poly_lt (poly1 poly2 : Polynomial) : Prop :=
   match poly1 with
   | poly_nil => poly2 <> poly_nil
   | poly_cons n1 tail1 =>
     match poly2 with
     | poly_nil => False
     | poly_cons n2 tail2 =>
       (n1 < n2 /\ poly_eq tail1 tail2) \/ poly_lt tail1 tail2
     end
   end.

 Fixpoint poly_le (poly1 poly2 : Polynomial) : Prop :=
   match poly1 with
   | poly_nil => True
   | poly_cons n1 tail1 =>
     match poly2 with
     | poly_nil => False
     | poly_cons n2 tail2 =>
       (n1 <= n2 /\ poly_le tail1 tail2) \/ poly_lt tail1 tail2
     end
   end.


 Functional Scheme poly_succ_ind := Induction for poly_succ Sort Prop.
 Functional Scheme poly_eval_ind := Induction for poly_eval Sort Prop.
 Functional Scheme poly_add_ind := Induction for poly_add Sort Prop.
 Functional Scheme poly_tail_ind := Induction for poly_tail Sort Prop.
 Functional Scheme poly_change_ind := Induction for poly_change Sort Prop.
 Functional Scheme poly_le_ind := Induction for poly_le Sort Prop.

 Fixpoint tail (poly:Polynomial) : Polynomial :=
   match poly with
   | poly_nil => poly_nil
   | poly_cons n tail => tail
   end.  

 Theorem poly_eq_self :
   forall (poly1 : Polynomial),
     poly_eq poly1 poly1.
 Proof.
   intros.
   induction poly1.
   simpl. auto.
   simpl.
   auto.
   Qed.

 Theorem poly_eq_if_equal :
   forall (poly1 poly2 : Polynomial),
     poly1 = poly2 -> poly_eq poly1 poly2.
 Proof.
   intros.
   rewrite H.
   induction poly2.
   simpl. auto.
   simpl.
   split.
   auto.
   apply poly_eq_self.
   Qed.

 Theorem tail_composition :
   forall (poly1 poly2 : Polynomial),
     forall (n:nat),
       poly_eq poly1 (poly_cons n poly2) -> poly_eq (tail poly1) poly2.
 Proof.
   intros.
   induction poly1.
   simpl in H.
   discriminate H.
   simpl in H.
   simpl.
   decompose [and] H.
   apply H1.
   Qed.

 Theorem equal_if_poly_eq :
   forall (poly1 poly2 : Polynomial),
     poly_eq poly1 poly2 -> poly1 = poly2.
 Proof.
   intro.
   induction poly1.
   intros.
   simpl in H.
   auto.

   intro.
   induction poly2.

   intros.
   simpl in H. contradiction.

   intros.

   simpl in H.    
   decompose [and] H.

   apply IHpoly1 in H1.
   rewrite H0.
   rewrite H1.
   tauto.
   Qed.

 Theorem poly_eq_implies_poly_le :
   forall (poly1 poly2 : Polynomial),
     poly_eq poly1 poly2 -> poly_le poly1 poly2.
 Proof.
   intro.
   induction poly1.
   intros.
   simpl. auto.
   intros.
   induction poly2.
   unfold poly_eq in H.
   contradiction.  
   simpl in H.
   decompose [and] H.
   simpl.
   left.
   split.
   rewrite H0. apply le_n.
   apply IHpoly1 in H1.
   auto.
   Qed.

 Theorem poly_lt_implies_poly_le :
   forall (poly1 poly2 : Polynomial),
     poly_lt poly1 poly2 -> poly_le poly1 poly2.
 Proof.
   intro.
   induction poly1.
   simpl. auto.
   intros.
   induction poly2.

   unfold poly_lt in H.
   contradiction.
   simpl in H.
   destruct H.
   decompose [and] H.

   simpl.
   left.
   split.
   apply lt_le_weak.
   auto.
   apply poly_eq_implies_poly_le. auto.
   simpl.
   right.
   auto.
   Qed.

Theorem Sn_eq_plus_one :
  forall (n:nat),
    S n = n+1.
Proof.
  intros.
  induction n.
  simpl. auto.
  simpl.
  rewrite IHn.
  auto.
  Qed.

 Theorem nat_lt_n_plus_one :
   forall (n:nat),
     n < n+1.
 Proof.
   induction n.
   auto.
   simpl.
   apply lt_n_S.
   apply IHn.
   Qed.

 Theorem n_ne_n_plus_1 :
   forall (n:nat),
     n <> n+1.
 Proof.
   intros.
   induction n.
   simpl. auto.
   simpl.
   rewrite <- Sn_eq_plus_one.
   auto.
   Qed.

 Theorem poly_le_implies_poly_lt_or_poly_eq :
   forall (poly1 poly2 : Polynomial),
     poly_le poly1 poly2 -> poly_lt poly1 poly2 \/ poly_eq poly1 poly2.
 Proof.
   intro.
   induction poly1.
   intros.

   induction poly2.  
   right. apply poly_eq_self.
   left.
   simpl.
   discriminate.

   intros.
   induction poly2.
   simpl in H. contradiction.

   simpl in H.
   simpl.
   destruct H.

   decompose [and] H.
   apply IHpoly1 in H1.
   destruct H1.  
   left.
   right.
   auto.
   apply equal_if_poly_eq in H1.
   rewrite H1.
   apply le_lt_or_eq in H0.
   destruct H0.
   left.
   left.
   split.
   auto.
   apply poly_eq_self.

   right.
   split.
   apply H0.
   apply poly_eq_if_equal.
   auto.

   left. right.
   apply H.
   Qed.

 Theorem poly_le_iff_poly_lt_or_poly_eq :
   forall (poly1 poly2 : Polynomial),
     poly_le poly1 poly2 <-> poly_lt poly1 poly2 \/ poly_eq poly1 poly2.
 Proof.
   intros.
   split.
   apply poly_le_implies_poly_lt_or_poly_eq.
   intro.
   destruct H.
   apply poly_lt_implies_poly_le.
   auto.
   apply poly_eq_implies_poly_le.
   auto.
   Qed.  

Theorem poly_succ_ne :
  forall (poly:Polynomial) (scale:nat),
    poly_succ poly scale <> poly.
Proof.
  intro.
  induction poly.
  intros.
  simpl.
  discriminate.
  intros.
  simpl.
  remember (n+1 <? scale) as b.
  induction b.
  injection.
  intro.
  apply n_ne_n_plus_1 with (n := n).
  auto.

  injection.
  intros.
  apply IHpoly in H0.
  auto.
  Qed.
 
Theorem poly_succ_lt :
  forall (poly:Polynomial) (scale:nat),
    poly_lt poly (poly_succ poly scale).
Proof.
  intro.
  induction poly.
  discriminate.

  induction scale.
  simpl.
  right.
  apply IHpoly.
  
  assert (poly_lt poly (poly_succ poly (S scale))).
  apply IHpoly.
  simpl.
  remember (n+1 <? S scale).
  induction b.
  simpl in IHscale.
  remember (n+1 <? scale).
  induction b.
  apply IHscale.
  destruct IHscale.
  decompose [and] H0.
  apply lt_n_0 in H1.
  contradiction.

  left.
  split.
  apply nat_lt_n_plus_one.  
  apply poly_eq_self.

  right.
  apply H.
  Qed.

Theorem false_ltb_implies_ge :
  forall a b : nat,
    false = (a <? b) -> a >= b.
Proof.
  admit.
  Qed.

(* Theorem poly_succ_eq_poly_plus_one : *)
(*   forall scale : nat, *)
(*     forall poly : Polynomial, *)
(*       poly_succ poly scale = poly_add (poly_cons 1 poly_nil) scale. *)
(*    poly_eval (poly_add (poly_cons 1 poly_nil) n scale) scale = *)
(*    S (poly_eval (poly_add poly_nil n scale) scale) *)

Theorem poly_succ_nat_succ :
  forall scale : nat,
    forall poly : Polynomial,
      poly_is_scale poly scale ->
        poly_eval (poly_succ poly scale) scale = S (poly_eval poly scale).
Proof.
  intros.
  induction poly.
  simpl.
  auto.
  simpl. 
  remember (n+1 <? scale).
  induction b.
  simpl.
  assert (n+1 = S n).
  symmetry.
  apply Sn_eq_plus_one.
  rewrite H0.
  auto.

  simpl.
  rewrite IHpoly.
  rewrite mult_succ_r.
  apply false_ltb_implies_ge in Heqb.
  simpl in H.
  decompose [and] H.
  unfold lt in H0.
  rewrite -> Sn_eq_plus_one in H0.
  assert (scale = n+1).
  apply le_antisym.
  apply Heqb.
  apply H0.
  rewrite Sn_eq_plus_one.
  remember (n + scale * poly_eval poly scale + 1).

  rewrite plus_comm in Heqn0.
  rewrite plus_permute in Heqn0.
  rewrite plus_assoc in Heqn0.
  rewrite plus_comm.  
  rewrite <- H2 in Heqn0.
  auto.

  simpl in H.
  decompose [and] H.  
  apply H1.
  Qed.

Theorem poly_add_poly_succ :
  forall (n scale : nat),
    forall (poly:Polynomial),
      poly_add poly (S n) scale = poly_add (poly_succ poly scale) n scale.
Proof.
  intro.
  induction n.
  intros.
  simpl. auto.
  intros.
  simpl.
  auto.
  Qed.
 
Theorem poly_succ_plus :
  forall (n scale:nat),
    forall (poly:Polynomial),
      poly_succ (poly_add poly n scale) scale = poly_add (poly_succ poly scale) n scale.
Proof.
  intro. intro.
  induction n.
  intros.
  simpl. auto.
  simpl.
  intro.
  apply IHn with (poly := poly_succ poly scale).
  Qed.    

Theorem poly_succ_preserves_is_scale :
  forall (scale:nat),
    forall (poly:Polynomial),
      scale > 1 -> poly_is_scale poly scale -> poly_is_scale (poly_succ poly scale) scale.
Proof.
  intro. intro.
  induction poly.
  intros.
  simpl. split. auto. auto.

  intros.
  simpl.
  remember (n+1 <? scale).
  induction b.  
  simpl.
  split.
  symmetry in Heqb.
  apply ltb_lt.
  assumption.
  simpl in H0.
  decompose [and] H0.
  apply H2.

  simpl.
  split.
  auto with arith.
  apply false_ltb_implies_ge in Heqb.
  apply IHpoly in H.
  apply H.
  simpl in H0.
  decompose [and] H0.
  apply H2.
  Qed.
  
Theorem poly_add_is_scale :
  forall (n scale:nat),
    scale > 1 -> poly_is_scale (poly_add poly_nil n scale) scale.
Proof.
  intros.
  induction n.  
  simpl. auto.
  simpl. fold (poly_succ poly_nil scale).
  rewrite <- poly_succ_plus.
  apply poly_succ_preserves_is_scale.
  auto.  
  auto.
  Qed.

Theorem poly_nat_iso :
  forall (n scale:nat),
    scale > 1 -> poly_eval (poly_add poly_nil n scale) scale = n.
Proof.    
  intros.
  induction n.
  simpl. auto.
  simpl.
  fold (poly_succ poly_nil scale).
  rewrite <- poly_succ_plus.
  rewrite poly_succ_nat_succ.
  rewrite IHn.
  auto.

  apply poly_add_is_scale.
  auto.
  Qed.

Theorem poly_prop_succ :
  forall n scale : nat,
    scale > 1 -> poly_eval (poly_lift n scale) scale = n.
Proof.
  intros.
  induction n.
  intros.
  simpl. auto.
  unfold poly_lift.
  apply poly_nat_iso.
  auto.
  Qed.
 

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