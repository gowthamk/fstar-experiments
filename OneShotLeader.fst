module OneShotLeader

module M = FStar.Map

module S = FStar.Set

module L = ListQ

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
           [SMTPat (is_quorum q1); 
            SMTPat (is_quorum q2)]
let axm_quorum_intersection q1 q2 = admit()

(*
 * Quorum monotonicity axiom. This cannot be proven just from quorum intersection since the lemma only goes one way.
 *)
val axm_quorum_monotonic: q1:list Node.t -> q2:list Node.t
  -> Lemma(requires (is_quorum q1) 
            /\ (forall x. (*{:pattern (L.mem n q1); (L.mem n q2)}*)
                  L.mem x q1 ==> L.mem x q2))
          (ensures is_quorum q2)
          [SMTPat (is_quorum q1);
           SMTPat (is_quorum q2)]
let axm_quorum_monotonic q1 q2 = admit()

val foo_thm: q1:list Node.t -> q2:list Node.t
  -> Lemma(requires (is_quorum q1) 
            /\ (forall x. (*{:pattern (L.mem n q1); (L.mem n q2)}*)
                  L.mem x q1 ==> L.mem x q2))
          (ensures is_quorum q2)
let foo_thm q1 q2 = 
  let _ = axm_quorum_monotonic q1 q2 in
  ()

let is_safe {leader} = 
  forall n1 n2. {:pattern (M.sel leader n1);(M.sel leader n2)} 
      M.sel leader n1 = None \/ M.sel leader n2 = None 
                \/ M.sel leader n1 = M.sel leader n2

let inv2 {msgs;votes} (n:Node.t) =
    L.mem (Leader n) msgs ==> is_quorum (M.sel votes n)

let inv3 ({leader;msgs}) (n1:Node.t) (n2:Node.t) =
  (M.sel leader n1 = Some n2) ==> L.mem (Leader n2) msgs

let inv4 ({votes;msgs}) (n1:Node.t) (n2:Node.t) = 
  L.mem n2 (M.sel votes n1)  ==> L.mem (Vote n2 n1) msgs

let inv5 ({msgs}) (n1:Node.t) (n2:Node.t) (n3:Node.t) = 
  L.mem (Vote n1 n2) msgs /\ L.mem (Vote n1 n3) msgs  
        ==> n2 = n3

#set-options "--query_stats --split_queries always"
#set-options "--z3rlimit 1000"

(*
 * Initial state and its safety
 *)
let init_state = {leader = M.const None;
                  voted = M.const false;
                  votes = M.const [];
                  msgs = []}

val init_state_safe: (n:Node.t) ->
  Lemma (is_safe init_state /\ inv2 init_state n)
let init_state_safe n = ()


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

val cast_vote_safe: n:Node.t -> s:state 
    -> n2:Node.t -> n3:Node.t -> n4:Node.t
    -> n5:Node.t -> n6:Node.t -> n7:Node.t
    -> n8:Node.t -> n9:Node.t -> 
    Lemma(requires is_safe s /\ inv2 s n2 /\ inv3 s n3 n4
                    /\ inv4 s n5 n6 /\ inv5 s n7 n8 n9)
         (ensures is_safe (cast_vote n s) 
               /\ inv2 (cast_vote n s) n2
               /\ inv3 (cast_vote n s) n3 n4
               /\ inv4 (cast_vote n s) n5 n6 
               /\ inv5 (cast_vote n s) n7 n8 n9)
let cast_vote_safe n s n2 n3 n4 n5 n6 n7 n8 n9 = ()

(* recv_vote *)

val recv_vote: s:state -> s':state{
       (forall n x.  L.mem x (M.sel s.votes n) 
            ==> L.mem x (M.sel s'.votes n)) 
    /\ (forall n. L.mem (Leader n) s'.msgs ==> L.mem (Leader n) s.msgs)}
let recv_vote s = 
  let is_my_vote m = match m with
    | Vote frm to -> (to = self) && not(L.mem frm (M.sel s.votes self))
    | _ -> false in
  let my_vote = L.find is_my_vote s.msgs in
  match my_vote with
    | Some (Vote frm _) -> 
      let votes' = M.upd s.votes self 
            (L.concat [frm] (M.sel s.votes self)) in
      {s with votes=votes'}
    | _ -> s
(*val recv_vote_monotonic_msgs: s:state -> n:Node.t
  -> Lemma(L.mem (Leader n) s.msgs 
            <==> L.mem (Leader n) (recv_vote s).msgs)
            [SMTPat (L.mem (Leader n) s.msgs)]
let recv_vote_monotonic_msgs s n = ()*)

val recv_vote_safe: s:state -> n1:Node.t ->
    n2:Node.t -> n3:Node.t -> 
    Lemma(requires is_safe s /\ inv2 s n1 /\ inv3 s n2 n3)
         (ensures is_safe (recv_vote s) 
                /\ inv2 (recv_vote s) n1
                /\ inv3 (recv_vote s) n2 n3)
let recv_vote_safe s n1 n2 n3 = 
  (*let s' = recv_vote s in
  let _ = assert (L.mem (Leader n) s'.msgs ==> L.mem (Leader n) s.msgs) in
  let _ = assert (L.mem (Leader n) s.msgs ==> 
                    is_quorum (M.sel s.votes n)) in
  let _ = assert(forall x. L.mem x (M.sel s.votes n) 
                  ==> L.mem x (M.sel s'.votes n)) in
  let _ = assert((is_quorum (M.sel s.votes n) /\ 
                    (forall x. L.mem x (M.sel s.votes n) 
                        ==> L.mem x (M.sel s'.votes n)))
                  ==> is_quorum (M.sel s'.votes n)) in*)
  ()

(*
 * Declare Leader
 *)

val declare_leader: state -> state
let declare_leader s = 
  let my_votes = M.sel s.votes self in
  if is_quorum my_votes then
    {s with msgs = (Leader self)::s.msgs}
  else s

val declare_leader_safe: s:state -> n1:Node.t ->
   n2:Node.t -> n3:Node.t ->
    Lemma(requires is_safe s /\ inv2 s n1 /\ inv3 s n2 n3)
         (ensures is_safe (declare_leader s) 
                /\ inv2 (declare_leader s) n1
                /\ inv3 (declare_leader s) n2 n3)
let declare_leader_safe s n1 n2 n3 = ()


val register_leader: state -> state
let register_leader s = 
  match L.find (function (Leader _) -> true 
                        | _ -> false) s.msgs with
  | Some (Leader n) -> 
      {s with leader = M.upd s.leader self (Some n)}
  | _ -> s

val register_leader_safe: s:state -> n1:Node.t ->
    n2:Node.t -> n3:Node.t ->
    Lemma(requires is_safe s /\ inv2 s n1 /\ inv3 s n2 n3)
         (ensures is_safe (register_leader s)
                  /\ inv2 (register_leader s) n1
                  /\ inv3 (register_leader s) n2 n3)
let register_leader_safe s n1 n2 n3 = ()

let t = true
