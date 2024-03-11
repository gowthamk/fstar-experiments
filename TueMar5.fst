module TueMar5
(*#push-options "--log_queries" *)

let x = 2

let even (x:int):bool = x%2 = 0

type mynat = x:int{x>=0}

(*
 * Intrinsic proof: property is part of the type of the function.
*)
val fibonacci: nat -> Tot (x:nat{x>0})
let rec fibonacci n = 
  match n with
  | 0 -> 1
  | 1 -> 1
  | _ -> fibonacci(n-1) + fibonacci(n-2) 


(*
 * IH: m:nat{m<n} -> Lemma(fibonacci m > 0)
 * Extrinsic proof: property asserted as a separate lemma.
 *)
val fib_is_positive: n:nat -> Lemma (fibonacci n > 0)
let rec fib_is_positive n =
if (n<2) then () 
else (fib_is_positive(n-1))

val fib2: a:nat -> b:nat -> n:nat -> Tot nat (decreases n)
let rec fib2 a b n =
match n with
| 0 -> a
| _ -> fib2 b (a+b) (n-1)

let fibonacci2 n = fib2 1 1 n


(*
 *  m:nat{m<n} -> Lemma(fib2 b (a+b) m > 0)
 *)
val fib2_is_positive: a:nat -> b:nat -> n:nat ->
        Lemma(requires a>0 /\ b>0)
             (ensures fib2 a b n > 0)
             (decreases n)
let rec fib2_is_positive a b n = 
    if n = 0 then () else fib2_is_positive b (a+b) (n-1)


val fib2_is_positive': n:nat -> 
    Lemma (forall (a:nat) (b:nat).{:pattern (fib2 a b n)} a >0 /\ b >0 ==> fib2 a b n >0)
let rec fib2_is_positive' n = 
    if n=0 then () else fib2_is_positive' (n-1)






