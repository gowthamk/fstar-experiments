module Mytest
#push-options "--log_queries" 
#push-options "--z3smtopt '(set-option :smt.mbqi true)'"
#push-options "--z3smtopt '(set-option :smt.ematching true)'"

let x = 2

val myprop: nat -> prop
let myprop x = x == 2

val fib: a:nat -> b:nat -> n:nat -> Tot nat (decreases n)
let rec fib a b n =
match n with
| 0 -> a
| _ -> fib b (a+b) (n-1)
let fibonacci n = fib 1 1 n

(*
 * The inductive hypothesis here says:
 *      m:nat{m < n} -> Lemma (fib a b m > 0).
 * How do we generalize a and b so that we get stronger IH?
 *)
(*let rec fib_is_positive (a:nat) (b:nat) (n:nat)
    : Lemma (requires a > 0 /\ b > 0)
            (ensures fib a b n > 0) =
    if n = 0 then ()
    else fib_is_positive a b (n-1)*)

(*
 * The following generalizes the IH:
 *      m:nat{m >0 /\ m<n} -> Lemma (forall a b. (a > 0 /\ b >0) ==> fib a b m > 0)
 * No idea why it doesn't work.
 * Update: It works with a pattern annotation.
 * Pattern-based quantifier instantiation considers patterns modulo ground equalities. 
 * But why does this pattern work? The pattern that should work is `fib a b n`, which matches `fib b (a+b) (n-1)` with substitutions S = [a -> b; b -> (a+b); n -> n-1]. S applied on the body of the IH is the ground term we want to discharge the theorem. 
 *)

 val fib_is_positive (n:nat)
    : Lemma (forall a b. {:pattern (fib b (a+b) (n-1))} (a > 0 /\ b >0) ==> fib a b n > 0)
let rec fib_is_positive n = 
    if n = 0 then ()
    else fib_is_positive (n-1)


val fib2: a:nat{a>0} -> b:nat{b>0} -> n:nat -> Tot (x:nat{x > 0}) (decreases n)
let rec fib2 a b n =
match n with
| 0 -> a
| _ -> fib2 b (a+b) (n-1)
let fibonacci2 n = fib2 1 1 n


let l1: list nat = [1;2]

let rec append l1 l2 = match l1 with
    | [] -> l2
    | x::xs -> x::(append xs l2) 

val app_length (#a:Type) (l1: list a) (l2: list a) : 
    (Lemma (List.length (append l1 l2) = List.length l1 + List.length l2))
let rec app_length l1 l2 = match l1 with
    | [] -> ()
    | x::xs -> app_length xs l2 