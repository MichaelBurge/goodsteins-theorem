Require Import Coq.Numbers.Natural.Peano.NPeano.

Module Type RepresentationSig.
Parameter A : Type.
Parameter repr : nat -> nat -> A.
Parameter eval : A -> nat -> nat.

Axiom eq_eval_repr : forall n:nat, forall r:nat, eval (repr n r) r = n.
End RepresentationSig.

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
