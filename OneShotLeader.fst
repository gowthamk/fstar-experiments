module OneShotLeader

module M = FStar.Map

module S = FStar.Set

module L = FStar.List.Tot

open L

type msg = 
  | Vote: Node.t -> Node.t -> msg
  | Leader: Node.t -> msg

noeq type state = {leader: M.t Node.t (option Node.t);
                   voted: M.t Node.t bool;
                   votes: M.t Node.t (list Node.t);
                   msgs: list msg}

(*
 * Assume a node called selfd
 *)
assume val self: Node.t
(*
 * Assume a function to determine quorums
 *)
assume val is_quorum : list Node.t -> bool
(*
 * Quorum intersection axiom
 *)
val axm_quorum_intersection: q1: list Node.t -> q2: list Node.t 
  -> Lemma (requires is_quorum q1 && is_quorum q2)
           (ensures (exists n. {:pattern (L.mem n q1); (L.mem n q2)} 
                      L.mem n q1 /\ L.mem n q2))
           [SMTPat (is_quorum q1); SMTPat (is_quorum q2)]
let axm_quorum_intersection q1 q2 = admit()

(*
 * Quorum monotonicity axiom. This cannot be proven just from quorum intersection since the lemma only goes one way.
 *)
val axm_quorum_monotonic: q1:list Node.t -> q2:list Node.t
  -> n:Node.t
  -> Lemma(requires (is_quorum q1) 
            /\ (L.mem n q1 ==> L.mem n q2))
          (ensures is_quorum q2)
          [SMTPat [(L.mem n q1);(L.mem n q2)]]
let axm_quorum_monotonic q1 q2 = admit()

let is_safe {leader} = 
  forall n1 n2. {:pattern (M.sel leader n1);(M.sel leader n2)} 
      M.sel leader n1 = None \/ M.sel leader n2 = None 
                \/ M.sel leader n1 = M.sel leader n2

let inductive_inv {leader;msgs;votes} =
  forall n. {:pattern (Leader n)}
    L.mem (Leader n) msgs ==> is_quorum (M.sel votes n)

let inv = inductive_inv

#set-options "--query_stats --split_queries always"
#set-options "--z3rlimit 1000"

(*
 * Initial state and its safety
 *)
let init_state = {leader = M.const None;
                  voted = M.const false;
                  votes = M.const [];
                  msgs = []}

val init_state_safe: unit -> 
  Lemma (is_safe init_state /\ inv init_state)
let init_state_safe () = ()


(*
 * Actions and their safety
 *)
let cast_vote n s = 
  if not (M.sel s.voted self) then
    let msgs' = (Vote self n )::s.msgs in
    let voted' = M.upd s.voted self true in
    {s with voted=voted'; msgs=msgs'}
  else
    s

val cast_vote_safe: n:Node.t -> s:state ->
    Lemma(requires is_safe s /\ inv s)
         (ensures is_safe (cast_vote n s) 
               /\ inv (cast_vote n s))
let cast_vote_safe n s = ()

(* recv_vote *)
(* L.mem x (M.sel s.votes n) *)

val recv_vote: s:state -> s':state{forall n x.  L.mem x (M.sel s.votes n) 
            ==> L.mem x (M.sel s'.votes n)}
let recv_vote s = 
  let is_my_vote m = match m with
    | Vote frm to -> to = self
    | _ -> false in
  let (my_votes,rest) = L.partition is_my_vote s.msgs in
  match my_votes with
    | (Vote frm _)::other -> 
      let votes' = M.upd s.votes self ([frm]@(M.sel s.votes self)) in
      let msgs' = other@rest in
      {s with votes=votes'; msgs=msgs'}
    | _ -> s

let inv2 {leader;msgs;votes} (n:Node.t) =
    L.mem (Leader n) msgs ==> is_quorum (M.sel votes n)

val recv_vote_monotonic: s:state -> n:Node.t
  -> Lemma(forall x. L.mem x (M.sel s.votes n) 
            ==> L.mem x (M.sel (recv_vote s).votes n))
            [SMTPat (is_quorum (M.sel s.votes n))]
let recv_vote_monotonic s n = ()

val recv_vote_safe: s:state -> n:Node.t ->
    Lemma(requires is_safe s /\ inv2 s n)
         (ensures is_safe (recv_vote s) 
                /\ inv2 (recv_vote s) n)
let recv_vote_safe s n = ()

val declare_leader: state -> state
let declare_leader s = 
  let my_votes = M.sel s.votes self in
  if is_quorum my_votes then
    {s with msgs = (Leader self)::s.msgs}
  else s

val declare_leader_safe: s:state ->
    Lemma(requires is_safe s /\ inv s)
         (ensures is_safe (declare_leader s) 
                /\ inv (declare_leader s))
let declare_leader_safe s = ()


val register_leader: state -> state
let register_leader s = 
  match L.find (function (Leader _) -> true 
                        | _ -> false) s.msgs with
  | Some (Leader n) -> 
      {s with leader = M.upd s.leader self (Some n)}
  | _ -> s

val register_leader_safe: s:state ->
    Lemma(requires is_safe s)
         (ensures is_safe (register_leader s))
let register_leader_safe s = ()


