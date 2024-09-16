open! Core
open! Types

module MapableIntList = struct
  module T = struct
    type t = int list [@@deriving sexp, compare]
  end

  include Comparator.Make (T)
  include T
end

module ConSpire = struct
  module Offer = struct
    type t = {round: int; value: int list} [@@deriving sexp]
  end

  type config =
    { node_id: int
    ; acceptor_ids: int list
    ; quorum_limit: int
    ; recovery_quorum: int }
  [@@deriving sexp]

  type msg = Value of int | Offer of Offer.t | Answer of Offer.t
  [@@deriving sexp]

  type proposer =
    { lastOffer: Offer.t option
    ; answers: Offer.t Map.M(Int).t
    ; committed: (int * int list) option
    ; config: config [@sexp.opaque] }
  [@@deriving sexp]

  type acceptor = {lastOffer: Offer.t} [@@deriving sexp]

  type node = Proposer of proposer | Acceptor of acceptor [@@deriving sexp]

  let rec step node src msg : node * (node_id * msg) list =
    match node with
    | Proposer p ->
        let p', msgs = step_proposer p src msg in
        (Proposer p', msgs)
    | Acceptor a ->
        let a', msgs = step_acceptor a src msg in
        (Acceptor a', msgs)

  and step_acceptor acceptor src msg : acceptor * (node_id * msg) list =
    match msg with
    | Value _ | Answer _ ->
        Fmt.failwith "Should never receive either a value or answer"
    | Offer o ->
        let a' =
          if o.round > acceptor.lastOffer.round then {lastOffer= o}
          else acceptor
        in
        (a', [(src, Answer a'.lastOffer)])

  and step_proposer proposer src msg : proposer * (node_id * msg) list =
    match msg with
    | Value v when Option.is_none proposer.lastOffer ->
        let offer = Offer.{round= 0; value= [v]} in
        ( {proposer with lastOffer= Some offer}
        , List.map proposer.config.acceptor_ids ~f:(fun aid ->
              (aid, Offer offer) ) )
    | Answer a
      when Option.value_map proposer.lastOffer ~default:false ~f:(fun o ->
               o.round = a.round ) ->
        {proposer with answers= Map.set proposer.answers ~key:src ~data:a}
        |> check_commit |> check_propose
    | _ ->
        (proposer, [])

  and check_commit p =
    let value_counts =
      let empty : int Map.M(MapableIntList).t =
        Map.empty (module MapableIntList)
      in
      Map.fold p.answers ~init:empty ~f:(fun ~key:_ ~data:(a : Offer.t) map ->
          Map.update map a.value ~f:(function None -> 1 | Some c -> c + 1) )
    in
    let committed_round_o =
      Map.fold value_counts ~init:None ~f:(fun ~key:value ~data:count acc ->
          if count >= p.config.quorum_limit then (
            assert (Option.is_none acc) ;
            Some ((Option.value_exn p.lastOffer).round, value) )
          else acc )
    in
    { p with
      committed=
        ( match (p.committed, committed_round_o) with
        | None, None ->
            None
        | Some x, None | None, Some x ->
            Some x
        | Some (r1, v1), Some (r2, v2) ->
            assert ([%equal: int list] v1 v2) ;
            Some (min r1 r2, v1) ) }

  and check_propose p =
    if
      Option.is_some p.committed
      || Map.length p.answers < p.config.recovery_quorum
    then (p, [])
    else
      let value_counts =
        let empty : int Map.M(MapableIntList).t =
          Map.empty (module MapableIntList)
        in
        Map.fold p.answers ~init:empty ~f:(fun ~key:_ ~data:(a : Offer.t) map ->
            Map.update map a.value ~f:(function None -> 1 | Some c -> c + 1) )
      in
      let missing_responses =
        List.length p.config.acceptor_ids - Map.length p.answers
      in
      (* If not every value is uncommittable or not enough responses don't act *)
      if
        not
        @@ Map.for_all value_counts ~f:(fun c ->
               c + missing_responses < p.config.quorum_limit )
      then (p, [])
      else
        (* Every value is uncommittable *)
        let chosen_value =
          value_counts
          |> Map.fold
               ~init:(Set.empty (module Int))
               ~f:(fun ~key:v ~data:_ prev ->
                 List.fold v ~init:prev ~f:(fun acc v -> Set.add acc v) )
          |> Set.to_list
        in
        let lastOffer = Option.value_exn p.lastOffer in
        let offer = Offer.{round= lastOffer.round + 1; value= chosen_value} in
        ( {p with lastOffer= Some offer; answers= Map.empty (module Int)}
        , List.map p.config.acceptor_ids ~f:(fun aid -> (aid, Offer offer)) )

  let make_prop pid base_config =
    Proposer
      { lastOffer= None
      ; answers= Map.empty (module Int)
      ; committed= None
      ; config= {base_config with node_id= pid} }

  let make_acc = Acceptor {lastOffer= {round= -1; value= []}}
end

let%expect_test "conspire circuit" =
  let open ConSpire in
  let print_state node msgs =
    print_s [%message (node : node) (msgs : (node_id * msg) list)]
  in
  let p =
    make_prop 0
      { node_id= 0
      ; acceptor_ids= [4; 5; 6; 7]
      ; quorum_limit= 3
      ; recovery_quorum= 3 }
  in
  let a = make_acc in
  let p, msgs = step p 0 (Value 0) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 0) (value (0))))) (answers ()) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs
      ((4 (Offer ((round 0) (value (0))))) (5 (Offer ((round 0) (value (0)))))
       (6 (Offer ((round 0) (value (0))))) (7 (Offer ((round 0) (value (0))))))))
    |}] ;
  (* Acceptor responses *)
  let a, msgs = step a 0 (Offer {round= 1; value= [0]}) in
  print_state a msgs ;
  [%expect
    {|
    ((node (Acceptor ((lastOffer ((round 1) (value (0)))))))
     (msgs ((0 (Answer ((round 1) (value (0))))))))
    |}] ;
  let a, msgs = step a 0 (Offer {round= 0; value= [0]}) in
  print_state a msgs ;
  [%expect
    {|
    ((node (Acceptor ((lastOffer ((round 1) (value (0)))))))
     (msgs ((0 (Answer ((round 1) (value (0))))))))
    |}] ;
  (* Round 0 partial responses to propose *)
  let p, msgs = step p 4 (Answer {round= 0; value= [0]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 0) (value (0)))))
        (answers ((4 ((round 0) (value (0)))))) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 5 (Answer {round= 0; value= [1]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 0) (value (0)))))
        (answers ((4 ((round 0) (value (0)))) (5 ((round 0) (value (1))))))
        (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 6 (Answer {round= 0; value= [2]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 1) (value (0 1 2))))) (answers ()) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs
      ((4 (Offer ((round 1) (value (0 1 2)))))
       (5 (Offer ((round 1) (value (0 1 2)))))
       (6 (Offer ((round 1) (value (0 1 2)))))
       (7 (Offer ((round 1) (value (0 1 2))))))))
    |}] ;
  (* Round 1 full responses required *)
  let p, msgs = step p 4 (Answer {round= 1; value= [1; 2; 3]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 1) (value (0 1 2)))))
        (answers ((4 ((round 1) (value (1 2 3)))))) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 5 (Answer {round= 1; value= [1;2;3]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 1) (value (0 1 2)))))
        (answers
         ((4 ((round 1) (value (1 2 3)))) (5 ((round 1) (value (1 2 3))))))
        (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 6 (Answer {round= 1; value= [2;3;4]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 1) (value (0 1 2)))))
        (answers
         ((4 ((round 1) (value (1 2 3)))) (5 ((round 1) (value (1 2 3))))
          (6 ((round 1) (value (2 3 4))))))
        (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 7 (Answer {round= 1; value= [2;3;4]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 2) (value (1 2 3 4))))) (answers ()) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs
      ((4 (Offer ((round 2) (value (1 2 3 4)))))
       (5 (Offer ((round 2) (value (1 2 3 4)))))
       (6 (Offer ((round 2) (value (1 2 3 4)))))
       (7 (Offer ((round 2) (value (1 2 3 4))))))))
    |}] ;
  (* Round 2 commit *)
  let p, msgs = step p 4 (Answer {round= 2; value= [1;2;3]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 2) (value (1 2 3 4)))))
        (answers ((4 ((round 2) (value (1 2 3)))))) (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 5 (Answer {round= 2; value= [1;2;3;4]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 2) (value (1 2 3 4)))))
        (answers
         ((4 ((round 2) (value (1 2 3)))) (5 ((round 2) (value (1 2 3 4))))))
        (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 6 (Answer {round= 2; value= [1;2;3;4]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 2) (value (1 2 3 4)))))
        (answers
         ((4 ((round 2) (value (1 2 3)))) (5 ((round 2) (value (1 2 3 4))))
          (6 ((round 2) (value (1 2 3 4))))))
        (committed ())
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}] ;
  let p, msgs = step p 7 (Answer {round= 2; value= [1;2;3;4]}) in
  print_state p msgs ;
  [%expect
    {|
    ((node
      (Proposer
       ((lastOffer (((round 2) (value (1 2 3 4)))))
        (answers
         ((4 ((round 2) (value (1 2 3)))) (5 ((round 2) (value (1 2 3 4))))
          (6 ((round 2) (value (1 2 3 4)))) (7 ((round 2) (value (1 2 3 4))))))
        (committed ((2 (1 2 3 4))))
        (config
         ((node_id 0) (acceptor_ids (4 5 6 7)) (quorum_limit 3)
          (recovery_quorum 3))))))
     (msgs ()))
    |}]
