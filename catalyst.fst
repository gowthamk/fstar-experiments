module Catalyst

module S = FStar.Set


val set_equal: #a:eqtype -> S.set a -> S.set a -> prop
let set_equal #a s1 s2 = forall x. S.mem x s1 <==> S.mem x s2

let (=.) = set_equal

val mem : #a:eqtype -> list a -> S.set a
let rec mem #a l = match l with
  | [] -> S.empty
  | x::xs -> S.add x (mem xs)


val dotp : #a:eqtype -> x:a -> l:list a 
        -> s:(S.set (a&a)){forall y. {:pattern (S.mem (x,y) s)}
                S.mem y (mem l) <==> S.mem #(a&a) (x,y) s}
let rec dotp #a x l = match l with
  | [] -> S.empty
  | y::ys -> S.add (x,y) (dotp x ys)

val dotp_is_correct: #a:eqtype -> x:a -> l:list a -> y:a -> z:a
        -> Lemma ((y = x && S.mem z (mem l))
                    == S.mem (y,z) (dotp x l))
                 [SMTPat (S.mem (y,z) (dotp x l))]
let rec dotp_is_correct #a x l y z =
  match l with
  | [] -> ()
  | hd :: tl ->
    dotp_is_correct x tl y z

val cartp: #a:eqtype -> list a -> list a -> S.set (a&a)
let rec cartp #a l1 l2 = match l1 with
  | [] -> S.empty #(a&a)
  | x::xs -> S.union (dotp x l2) (cartp xs l2)

val cartp_prop: #a:eqtype -> list a -> list a -> S.set (a&a) -> prop
let cartp_prop #a l1 l2 s = 
    forall x y. S.mem (x,y) s <==> S.mem x (mem l1) /\ S.mem y (mem l2)  

#push-options "--query_stats --split_queries always"
#set-options "--z3rlimit 1000"

val cartp_is_correct:  #a:eqtype -> l1:list a -> l2:list a
  -> Lemma (cartp_prop l1 l2 (cartp l1 l2))
let rec cartp_is_correct l1 l2 = match l1 with
  | [] -> ()
  | x::xs -> cartp_is_correct xs l2


val ord : #a:eqtype -> list a -> S.set (a & a)
let rec ord #a l = match l with
  | [] -> S.empty
  | x::xs -> S.union (dotp x xs) (ord xs)

