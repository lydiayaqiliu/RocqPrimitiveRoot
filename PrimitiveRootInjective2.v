
Require Import ZArith List Lia.
Require Import FMaps FMapAVL FMapFacts OrderedTypeEx.
Import ListNotations.

(*Another easier way we could prove that Primitive root is injective is through
finite map. Indeed, by definition, primitive root is surgective to 
1 <= a < p and forall 0 < i <= p-1. Since they have the same cardinality,
they must also be injective.*)

(*This is unfinished. This is a simpler way to prove injectivity using
surjectivity on A -> B if |A| <= |B| ==> bijectivity. But I do not 
have time to finish it; please dont count this as a part of my final project TT. 
Just pushing it to the repo so i can save it for later as a fun practice. *)


Module ZMap := FMapAVL.Make(Z_as_OT).
Module ZMapFacts := FMapFacts.Facts(ZMap).
Module ZMapProps := FMapFacts.Properties(ZMap).

(*Piegon hole*)

Fixpoint find_index (f : nat -> nat) (v : nat) (n : nat) : option nat :=
  match n with
  | O    => if Nat.eq_dec (f O) v then Some O else None
  | S n' =>
      if Nat.eq_dec (f (S n')) v
      then Some (S n')
      else find_index f v n'
  end.

Lemma find_index_sound :
  forall f v n i,
  find_index f v n = Some i ->
  i <= n /\ f i = v.
Proof.
  intros f v n.
  induction n as [|n' IH]; intros i Hfind; simpl in Hfind.
  - destruct (Nat.eq_dec (f 0) v) as [Heq|]; inversion Hfind; subst.
    split; try(lia).
  - destruct (Nat.eq_dec (f (S n')) v) as [Heq|Hne].
    + inversion Hfind; subst. split; try(lia).
    + apply IH in Hfind. destruct Hfind. split; try(lia).
Qed.

Lemma find_index_complete :
  forall f v n i,
  i <= n -> f i = v ->
  exists j, find_index f v n = Some j.
Proof.
  intros f v n.
  induction n as [|n' IH]; intros i Hi Hfi.
  - simpl. destruct (Nat.eq_dec (f 0) v).
    + exists 0. reflexivity.
    + exfalso. apply n. rewrite <- Hfi. f_equal. lia.
  - simpl. destruct (Nat.eq_dec (f (S n')) v) as [|Hne].
    + exists (S n'). reflexivity.
    + destruct (Nat.eq_dec i (S n')) as [Heqi|Heqi].
      * exfalso. apply Hne. rewrite <- Heqi. exact Hfi.
      * apply IH with (i := i); try(lia).
Qed.

(*Piegon hole*)

Search(le).

(* If we have n+1 elements mapping into n slots,
   two elements must share a slot *)
Lemma pigeonhole_nat :
  forall (n : nat) (f : nat -> nat),
  (forall i, i <= n -> f i < n) ->
  exists i j, i < j /\ j <= n /\ f i = f j.
Proof.
  induction n.
  - (* n=0: f maps into empty range, contradiction *)
    intros.
    exfalso.
    specialize (H 0 (le_n 0)).
    lia.
  - intros.
    (* Check if any earlier element shares value with f(n+1) *)
    destruct (find_index f (f (S n)) n) eqn:Hfind.
    + (*if found*)
        apply find_index_sound in Hfind. destruct Hfind as [Hn0 Heq].
        exists n0, (S n). lia.
    (* not found *)
    + assert (Hf'range : forall k, k <= n ->
  (  fun k => if f k <? f (S n) then f k else f k - 1) k < n).
        { intros k Hk. simpl.
        assert (Hfk : f k < S n) by (apply H; lia).
        destruct (f k <? f (S n)) eqn:Hlt.
        - apply Nat.ltb_lt in Hlt.
            assert (HfSn : f (S n) < S n) by (apply H; lia).
            lia.
        - apply Nat.ltb_nlt in Hlt.
            assert (Hne : f k <> f (S n)).
            { intro Heq.
            destruct (find_index_complete f (f (S n)) n k Hk Heq)
                as [m Hm].
            rewrite Hm in Hfind. discriminate. }
            lia. } 

    destruct (IHn  (fun k => if f k <? f (S n) then f k else f k - 1)
                Hf'range)
    as [k [j [Hij [Hjn Heq]]]].
    exists k,j.
    split; try(lia). split; try(lia). 
    (* Recover f i = f j from the squeezed equality *)
    destruct (f k <? f (S n)) eqn:Ek;
    destruct (f j <? f (S n)) eqn:Ej.
    * lia.
    * (* f k < f(Sn), f j >= f(Sn) *)
    apply Nat.ltb_lt  in Ek.
    apply Nat.ltb_nlt in Ej.
    assert (Hnej : f j <> f (S n)).
    { intro Heq2.
        destruct (find_index_complete f (f (S n)) n j Hjn Heq2)
        as [m Hm].
        rewrite Hm in Hfind. discriminate. }
    lia.
    * (* f i >= f(Sn), f j < f(Sn) *)
    apply Nat.ltb_nlt in Ek.
    apply Nat.ltb_lt  in Ej.
    assert (Hnei : f k <> f (S n)).
    { intro Heq2.
        assert (Hi' : k <= n) by lia.
        destruct (find_index_complete f (f (S n)) n k Hi' Heq2)
        as [m Hm].
        rewrite Hm in Hfind. discriminate. }
    lia.
    * (* f i >= f(Sn), f j >= f(Sn) *)
    (* f k - 1 = f j - 1 (and both not zero)*)
    apply Nat.ltb_nlt in Ek.
    apply Nat.ltb_nlt in Ej.
    assert (Hnei : f k <> f (S n)).
    { intro Heq2.
        assert (Hk: k <= n) by lia.
        destruct (find_index_complete f (f (S n)) n k Hk Heq2)
    as [m Hm].
        rewrite Hm in Hfind. discriminate. }
    assert (Hnej : f j <> f (S n)).
    { intro Heq2.
        destruct (find_index_complete f (f (S n)) n j Hjn Heq2)
        as [m Hm].
        rewrite Hm in Hfind. discriminate. }
  (* Now f i > f(S n) and f j > f(S n), so both >= 1 *)
  (* f i - 1 = f j - 1 and both > 0 => f i = f j *)
  lia.
    Qed.

(*Now lets prove surjectivity*)

