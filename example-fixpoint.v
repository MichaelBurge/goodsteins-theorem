Require Import Coq.Arith.Plus.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Arith.
Require Import Peano.
Fixpoint factorial n :=
  match n with
  | 0 => 1
  | S x => n * (factorial x)
  end.

Functional Scheme factorial_ind := Induction for factorial Sort Prop.
 
Theorem snn_le_sn :
  forall k n, S n ^ k >= n ^ k.
Proof.
  induction k.
  intros.
  simpl.  
  auto.
  intros.
  simpl.  
  assert (S n ^ k >= n^k).
  apply IHk.
  assert (S n ^ k + n * S n ^ k >= n * S n ^ k).
  omega.
  assert (n * S n ^ k >= n * n ^ k).
  apply mult_le_compat_l.
  apply H.
  omega.
  Qed.

Theorem factorial_example :
  forall n, n^n >= factorial n.
Proof.
  intros.
  functional induction factorial n.
  auto.
  assert ((S x) ^ (S x) >= (S x) ^ x).
  simpl.
  assert (S x ^ x + x * S x ^ x >= S x ^ x + 0).
  apply plus_le_compat_l with (p := S x ^ x) (m := x * S x ^ x) (n := 0).
  apply le_0_n.
  omega.
  assert (S x * x^x >= S x * factorial x).
  apply mult_le_compat_l.
  apply IHn0.
  assert (S x ^ S x >= S x * x ^ x).
  assert (S x ^ x >= x ^ x).
  simpl.
  apply snn_le_sn.
  assert (S x * S x ^ x >= S x * x ^ x).
  apply mult_le_compat_l.
  apply snn_le_sn.
  apply H2.
  omega.
  Qed.
