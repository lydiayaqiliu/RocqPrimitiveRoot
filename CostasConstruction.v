Require Import Coq.ZArith.Zdiv.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Require Import Recdef.
Require Import Bool.

Open Scope Z_scope.


(*
  Before everything, we want to be able to show whether numbers like 3, 7, 89 are prime.
  To do that, we need some basic tools. 
  The inspriation is from this post on stack exchange:
  https://stackoverflow.com/questions/49282773/how-to-prove-that-a-number-is-prime-using-znumtheory-in-coq

  For_all is used to check whether a statement is true for all number less than n.
  This would be useful to computationally determine whether a number is a prime.
  for_all_spec is just a convienient lemma that facilitates correctness proof.
  is_prime is defined such that is_prime n = true if forall n' < n, the 
    gcd of n and n' is always 1.
  Finally, we check this is_prime definition do correspond to the prime definition
    in Z.numtheory.
*)

Function for_all (f:Z->bool) n {measure Z.to_nat n}:=
  if n <=? 1 then true
  else f (n-1) && for_all f (n-1).
Proof.
intros H n H1. apply Z2Nat.inj_lt; apply Z.leb_nle in H1; lia.
Defined.



Lemma for_all_spec : forall f n,
  for_all f n = true -> forall k, 1 <= k < n -> f k = true.
Proof.
    intros. 
    functional induction (for_all f n).
    + lia.
    + rewrite for_all_equation in *. apply andb_true_iff in H as [Hfp  Hfred]. 
    destruct (Z.eq_dec k (n - 1)) as [Heq | Hneq].
        * subst. apply Hfp.
        * subst. apply IHb.
            ** apply Hfred.
            ** lia.
Qed. 


Definition is_prime (p:Z) :=
  (1 <? p) && for_all (fun k => Z.gcd k p =? 1) p.


Theorem is_prime_correct : forall z, is_prime z = true -> prime z.
Proof.
    intros. unfold is_prime in H.
    apply andb_true_iff in H.
    destruct H as [H1 H2]. constructor.
    lia. intros. apply for_all_spec with (k := n) in H2.
        + unfold rel_prime. apply Z.eqb_eq in H2. rewrite <- H2.
        apply Zgcd_is_gcd.
    + assumption.
Qed.
        
(*By this definition, can check whether 89 is prime.  *)

Example p89 : prime 89.
Proof. apply is_prime_correct. reflexivity. Qed.

(*Indeed it is.*)


(*We need a helper that facilates our check for prime number & primitive root*)




Definition coprime (a b: Z) :Prop := Z.gcd a b = 1.

Definition is_coprime (a b : Z) := fun a b => (Z.gcd a b =? 1).


Example coprime389: coprime 3 89.
Proof. reflexivity. Qed.

(*now define a primitive root. g is a primitive root mod p if for all 1 <= a < p,
if a and p are coprime, then there exists some i\in (N\/{0}) such that g^i mod p = a.*)
Definition primitive_root (g p : Z) : Prop :=
    prime p /\
    coprime g p /\
    forall a : Z, 1 <= a < p -> coprime a p ->
    exists i : Z, 0 < i <= p-1 /\ ((g ^ i) mod p) = a.

(*Removed the -> to aviod vacuously true case*)
Fixpoint find_exp (g a p : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S n =>
      let i := Z.of_nat (S n) in
      if (g ^ i) mod p =? a 
      then Some i
      else find_exp g a p n
  end.

Definition check_primitive_root (g p fuel : Z) : bool :=
  for_all (fun a => 
    match find_exp g a p (Z.to_nat fuel) with
    | Some _ => true
    | None => false
    end) p.

Lemma find_exp_correct : forall g a p upbound i,
  find_exp g a p upbound = Some i ->
  0 < i <= Z.of_nat upbound /\ (g ^ i) mod p = a.
Proof.
  intros g a p upbound.
  induction upbound as [| n IHn].
  - simpl. intros. discriminate.
  - simpl. intros.
    destruct (Z.pow_pos g (PosDef.Pos.of_succ_nat n) mod p =? a) eqn:E.
    * simpl in H. injection H as <-. split.
      ** split.
        + rewrite Zpos_P_of_succ_nat. lia.
        + lia.
      ** apply Z.eqb_eq in E.
        rewrite Zpos_P_of_succ_nat.
        lia.
    * apply IHn in H.
    destruct H as [Hbound Hmod]. split.
      ** split.
        + lia.
        + rewrite Zpos_P_of_succ_nat. lia.
      ** assumption.
Qed.


Lemma check_primitive_root_correct : forall g p,
  check_primitive_root g p (p-1) = true ->
  forall a, 1 <= a < p -> coprime a p ->
  exists i, 0 < i <= p-1 /\ (g ^ i) mod p = a.
Proof.
  intros.
  unfold check_primitive_root in H.
  apply for_all_spec with (k := a) in H.
  - destruct (find_exp g a p (Z.to_nat (p-1))) eqn:Hfound.
    + apply find_exp_correct in Hfound. exists z. lia.
    + discriminate.
  - apply H0.
Qed.



Example three_is_a_primitive_root_mod_89: primitive_root 3 89.
Proof.
  unfold primitive_root. split. apply p89. split. apply coprime389.
  intros a H H0.
  apply check_primitive_root_correct.
  - reflexivity.
  - exact H.
  - exact H0.
Qed.

(*Introducing costats array. if (x, f(x)) is a costa array, then for all (x, f(x)), (y, f(y)),
(x-y) and (f(x)-f(y)) are distinct. Let x-y represent the difference in pitch (discretemized as keys
on piano), f(x) - f(y) be the difference in time, we would be able to construct a 'patternless' music.*)

(*Notice one improtant thing we need to use is that primitive root is actually injective. Lets
Admit it for now and see if we can prove it if we have time.*)

(*We acknowledge for now that primitive root is injective*)
Lemma primitive_root_injective : forall g p i k,
  primitive_root g p ->
  0 <= i < p - 1 ->
  0 <= k < p - 1 ->
  g ^ i mod p = g ^ k mod p ->
  i = k.
Proof.
Admitted.

Definition costas (f : Z -> Z) (n : Z) : Prop := 
    forall i j k l,
    0 < i /\ i < j /\ j <= n ->
    0 < k /\ k < l /\ l <= n ->
    j - i = l - k ->
    f j - f i = f l - f k ->
    i = k /\ j = l.

(*Welch construction of Costas*)

Lemma primitive_root_pow_ne_one : forall g p m,
  primitive_root g p ->
  0 < m < p - 1 ->
  g ^ m mod p <> 1.
Proof.
intros. replace (1) with (g^0 mod p).
- intros Hconrta.
apply primitive_root_injective in Hconrta.
  + lia.
  + assumption.
  + lia.
  + lia.
- replace (g ^ 0) with 1. 
  + apply Zmod_1_l. lia.
  + lia.
Qed.

Search ((_ - _) mod _ ).

(*Zmod_divide: forall a b : Z, b <> 0 ->
a mod b = 0 -> (b | a)
Gauss: ∀ a b c : Z, (a | b * c) → rel_prime a b → (a | c)
Z.mul_comm: forall n m : Z, n * m = m * n
Zdivide_mod: forall a b : Z, (b | a) -> a mod b = 0
Z.cong_iff_0:
forall a b m : Z, a mod m = b mod m <->
(a - b) mod m = 0
*)

Lemma mod_minus_distr : forall a b p,
  p > 1 ->
  (a - b) mod p = 0 ->
  a mod p = b mod p.
Proof.
  intros.
  apply Z.cong_iff_0. assumption.
Qed.



Lemma mod_cancel : forall p a b c,
  prime p ->
  c mod p <> 0 ->
  (a * c) mod p = (b * c) mod p ->
  a mod p = b mod p.
  (*Notice this is true p is a prime => Z/pZ is a field.*)
Proof.
  (*(a * c) mod p = (b * c) mod p ->
    ((a-b) * c) mod p = 0 ->
    (p | ((a-b) * c)) ->
    we know p does not divide p ->
    p | (a - b) ->
    (a - b) mod p = 0 ->
    a mod p - b mod p = 0 ->
    What we want.*)
  intros.
  assert (((a-b) * c) mod p = 0).
  {rewrite Z.mul_sub_distr_r. rewrite Zminus_mod. 
  rewrite H1. replace ((b * c) mod p - (b * c) mod p) with 0.
  apply Zmod_0_l. lia.
  }
  assert (p <> 0).
  { 
    apply prime_ge_2 in H. lia.
  }
  apply Zmod_divide in H2. 2: apply H3.
  rewrite Z.mul_comm in H2.
  assert (rel_prime p c).
  {
     apply prime_rel_prime. apply H. 
     intros contra. destruct H0. apply Zdivide_mod. apply contra.
  }
  apply Gauss in H2. 2: apply H4.
  apply Zdivide_mod in H2. 
  apply mod_minus_distr.
  apply prime_ge_2 in H. lia.
  assumption.
Qed.
  


  




Search (1 mod _ = 1).
(*
Z.mul_mod:
forall a b n : Z,
n <> 0 -> (a * b) mod n = (a mod n * (b mod n)) mod n*)


Theorem primitive_root_gives_costas :
  forall p g, prime p ->
  primitive_root g p ->
  costas (fun i => g^i mod p) (p - 1).
Proof.
  intros p g Hp Hprim.
  unfold costas.
  intros i j k l Hij Hkl Hdiff Hfeq.
  destruct Hij as [Hi [Hij Hj]].
  destruct Hkl as [Hk [Hkl Hl]].
  enough (Hik : i = k) by lia.
  - (* prove i = k *)
    (* step 1: g^(j-i) - 1 ≠ 0 mod p *)
    assert (Hne : g ^ (j - i) mod p <> 1).
    { apply primitive_root_pow_ne_one with (p := p).
      - exact Hprim.
      - lia. }

    (* prepare the factor to get g^i = g^k mod p *)
    assert (Hgigk : g ^ i mod p = g ^ k mod p).
    assert (Hfactor : g ^ i * (g ^ (j - i) - 1) mod p =
                  g ^ k * (g ^ (j - i) - 1) mod p).
{
  assert (Hlhs : g ^ i * (g ^ (j - i) - 1) = g ^ j - g ^ i).
{ rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_1_r.
  rewrite <- Z.pow_add_r by lia.
  replace (i + (j - i)) with j by lia.
  ring. }
  assert (Hrhs : g ^ k * (g ^ (j - i) - 1) = g ^ l - g ^ k).
{ rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_1_r.
  rewrite <- Z.pow_add_r by lia.
  replace (k + (j - i)) with l by lia.
  ring. }
  rewrite Hlhs. rewrite Hrhs.
  rewrite Zminus_mod. rewrite (Zminus_mod (g^l) (g^k)). 
  rewrite Hfeq. reflexivity.
  
}

  (*Try to cancel out same term in Hfactor*)
  apply mod_cancel with (p := p) (c := g ^ (j - i) - 1).
  assumption. 
  intros Hcontra. apply Hne.  
  2: assumption.
  (*Why no modular distributivity? That doesnt make sense at all.*)
  apply mod_minus_distr in Hcontra. apply prime_ge_2 in Hp. rewrite Z.mod_1_l in Hcontra.
  lia.
  + lia.
  + lia.
  + apply primitive_root_injective with (g := g) (p := p); try(assumption).
    * lia.
    * lia.
Qed.

(*Yet this is just a few lines proof on the paper!*)

Example patternless_music : costas (fun i => 3^i mod 89) (88).
Proof. apply primitive_root_gives_costas. 
    - apply p89.
    - apply three_is_a_primitive_root_mod_89.
Qed.

    
    