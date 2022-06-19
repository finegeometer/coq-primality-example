From Coq Require Import ssreflect ssrbool Lists.Streams.

(* Implementation *)

Definition composite (n : nat) : Prop := exists a b, n = S (S a) * S (S b).

CoFixpoint counter (n i : nat) : Stream bool :=
    match i with
    | 0 => Cons true (counter n n)
    | S i => Cons false (counter n i)
    end.

CoFixpoint sieve (n : nat) (stream : Stream bool) : Stream bool :=
    Cons (hd stream) (sieve (S n) (zipWith orb (tl stream) (counter n n))).

Definition composites := sieve 1 (const false).

Definition compositeb (n : nat) : bool :=
    match n with
    | 0 => false
    | 1 => false
    | S (S n) => Str_nth n composites
    end.

(* Correctness Proof *)

Lemma Str_nth_S {A} n (stream : Stream A) : Str_nth (S n) stream = Str_nth n (tl stream).
Proof.
    rewrite /Str_nth /Str_nth_tl.
    reflexivity.
Qed.

Lemma Str_nth_const {A} n (a : A) : Str_nth n (const a) = a.
Proof.
    by elim: n.
Qed.

Lemma counter_spec n i k : reflect (exists a, k = i + a * S n) (Str_nth k (counter n i)).
Proof.
    move: i; elim: k => [|k IH] i.
    - case: i => [|i].
        + left. by exists 0.
        + right. move=> [a //].
    - rewrite Str_nth_S; simpl.
        case: i => [|i].
        + apply /(iffP (IH n)).
            * move=> [a ->]. by exists (S a).
            * move=> [a].
                case: a => [// | a].
                move /(f_equal Nat.pred); simpl.
                by exists a.
        + apply /(iffP (IH i)).
            * move=> [a ->]. by exists a.
            * move=> [a /(f_equal Nat.pred)]. by exists a.
Qed.

Lemma sieve_spec P n stream k :
    reflect P (Str_nth k stream) ->
    reflect (P \/ exists a b, k = b + S a * S (b + n)) (Str_nth k (sieve n stream)).
Proof.
    move: P n stream; elim: k => [|k IH] P n stream H.
    - apply /(iffP H).
        + by left.
        + case=> [// | [a [b]]].
            rewrite -plus_n_Sm => //.
    - apply /(iffP (IH _ _ _ _)).
        + rewrite Str_nth_zipWith. apply /orP.
        + case; first case.
            * move /H. by left.
            * move /counter_spec => [a ->]. right. by exists a, 0.
            * move=> [a [b ->]]. right. exists a, (S b).
                by rewrite -(plus_n_Sm b n).
        + case.
            * move /H. by left; left.
            * move=> [a [b]].
                move /(f_equal Nat.pred); case: b => [|b]; simpl=>->.
                -- left; right. apply /counter_spec. by exists a.
                -- right. exists a, b.
                    by rewrite -(plus_n_Sm b n).
Qed.

Theorem compositeP n : reflect (composite n) (compositeb n).
Proof.
    case: n => [|n]; last case: n => [|n].
    - right. move=> [a [b //]].
    - right. move=> [a [b //]].
    - apply /(iffP (sieve_spec False 1 (const false) n _)).
        + rewrite Str_nth_const. by right.
        + case=>[// | [a [b ->]]].
            rewrite -(plus_n_Sm b 0) -(plus_n_O).
            by exists a, b.
        + move=> [a [b]].
            do 2 move /(f_equal Nat.pred); simpl=>->.
            right; exists a, b.
            by rewrite -(plus_n_Sm b 0) -(plus_n_O).
Qed.
