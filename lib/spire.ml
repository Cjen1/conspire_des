open! Core
open! Types

module Spire = struct
  module Offer = struct
    type t = {round: int; value: int; primed: bool} [@@deriving sexp, compare]
  end

  type config = {node_id: int; acceptor_ids: int list; quorum_limit: int}
  [@@deriving sexp]

  type msg = Value of int | Offer of Offer.t | Answer of Offer.t
  [@@deriving sexp]

  type proposer =
    { lastOffer: Offer.t option
    ; answers: Offer.t Map.M(Int).t
    ; config: config
    ; primed_round_vals: Set.M(Int).t Map.M(Int).t }
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

  and step_proposer proposer src msg : proposer * (node_id * msg) list =
    match msg with
    | Value v when Option.is_none proposer.lastOffer ->
        let offer = Offer.{round= 0; value= v; primed= false} in
        ( {proposer with lastOffer= Some offer}
        , List.map proposer.config.acceptor_ids ~f:(fun aid ->
              (aid, Offer offer) ) )
    | Value _ ->
        (proposer, [])
    | Answer a ->
        let p =
          if a.primed then
            { proposer with
              primed_round_vals=
                Map.update proposer.primed_round_vals a.round ~f:(function
                  | None ->
                      Set.singleton (module Int) src
                  | Some s ->
                      Set.add s src ) }
          else proposer
        in
        if
          Option.value_map proposer.lastOffer ~default:false ~f:(fun o ->
              o.round = a.round )
        then
          check_propose
            {p with answers= Map.set proposer.answers ~key:src ~data:a}
        else (p, [])
    | Offer o ->
        Fmt.failwith "Received offer when cannot use it: %a" (fmt_sexp false)
          (Offer.sexp_of_t o)

  and check_propose proposer =
    if Map.length proposer.answers < proposer.config.quorum_limit then
      (proposer, [])
    else
      let value_counts =
        let empty : int Map.M(Int).t = Map.empty (module Int) in
        Map.fold proposer.answers ~init:empty
          ~f:(fun ~key:_ ~data:(a : Offer.t) map ->
            Map.update map a.value ~f:(function None -> 1 | Some c -> c + 1) )
      in
      (* omit primed count bc that is done later *)
      if Map.exists value_counts ~f:(fun c -> c >= proposer.config.quorum_limit)
      then
        let max_val =
          Map.fold value_counts ~init:None ~f:(fun ~key ~data -> function
            | Some (mv, mc) when mc > data ->
                Some (mv, mc)
            | Some _ | None ->
                Some (key, data) )
          |> Option.value_exn |> fst
        in
        let offer =
          Offer.
            { round= (Option.value_exn proposer.lastOffer).round + 1
            ; value= max_val
            ; primed= true }
        in
        ( {proposer with lastOffer= Some offer; answers= Map.empty (module Int)}
        , List.map proposer.config.acceptor_ids ~f:(fun aid ->
              (aid, Offer offer) ) )
      else
        (* No unanimous response => pick any primed value otherwise choose random *)
        let primed_value =
          Map.fold proposer.answers ~init:None ~f:(fun ~key:_ ~data -> function
            | Some v -> Some v | None -> if data.primed then Some data else None )
          |> Option.map ~f:(fun o -> o.value)
        in
        let unprimed_values =
          Map.fold proposer.answers
            ~init:(Set.empty (module Int))
            ~f:(fun ~key:_ ~data s -> Set.add s data.value)
          |> Set.to_list
        in
        let value =
          Option.value primed_value
            ~default:
              (List.nth_exn unprimed_values
                 (proposer.config.node_id % List.length unprimed_values) )
        in
        let offer =
          Offer.
            { round= (Option.value_exn proposer.lastOffer).round + 1
            ; value
            ; primed= false }
        in
        ( {proposer with lastOffer= Some offer; answers= Map.empty (module Int)}
        , List.map proposer.config.acceptor_ids ~f:(fun aid ->
              (aid, Offer offer) ) )

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

  let make_prop pid base_config =
    Proposer
      { lastOffer= None
      ; answers= Map.empty (module Int)
      ; config= {base_config with node_id= pid}
      ; primed_round_vals= Map.empty (module Int) }

  let make_acc = Acceptor {lastOffer= {round= -1; value= -1; primed= false}}
end

let%expect_test "spire_circuit" =
  let open Spire in
  let print_state n msgs =
    Fmt.pr "%a@.%a@." (fmt_sexp false) (sexp_of_node n) (fmt_sexp false)
      ([%sexp_of: (node_id * msg) list] msgs)
  in
  let base_config = {node_id= 0; acceptor_ids= [3; 4; 5]; quorum_limit= 2} in
  let p = make_prop 0 base_config in
  let p, msgs = step p (-1) (Value 0) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 0) (value 0) (primed false)))) (answers ())
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ()))))
    (((3 (Offer ((round 0) (value 0) (primed false))))
     (4 (Offer ((round 0) (value 0) (primed false))))
     (5 (Offer ((round 0) (value 0) (primed false))))))
    |}] ;
  let p, msgs = step p 3 (Answer {round= 0; value= 0; primed= false}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 0) (value 0) (primed false))))
      (answers ((3 ((round 0) (value 0) (primed false)))))
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ()))))
    (())
    |}] ;
  let p, msgs = step p 4 (Answer {round= 0; value= 1; primed= false}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 1) (value 0) (primed false)))) (answers ())
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ()))))
    (((3 (Offer ((round 1) (value 0) (primed false))))
     (4 (Offer ((round 1) (value 0) (primed false))))
     (5 (Offer ((round 1) (value 0) (primed false))))))
    |}] ;
  let p, msgs = step p 5 (Answer {round= 0; value= 2; primed= false}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 1) (value 0) (primed false)))) (answers ())
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ()))))
    (())
    |}] ;
  let p, msgs = step p 4 (Answer {round= 1; value= 0; primed= false}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 1) (value 0) (primed false))))
      (answers ((4 ((round 1) (value 0) (primed false)))))
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ()))))
    (())
    |}] ;
  let p, msgs = step p 5 (Answer {round= 1; value= 2; primed= true}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 2) (value 2) (primed false)))) (answers ())
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ((1 (5)))))))
    (((3 (Offer ((round 2) (value 2) (primed false))))
     (4 (Offer ((round 2) (value 2) (primed false))))
     (5 (Offer ((round 2) (value 2) (primed false))))))
    |}] ;
  let p, msgs = step p 4 (Answer {round= 2; value= 2; primed= true}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 2) (value 2) (primed false))))
      (answers ((4 ((round 2) (value 2) (primed true)))))
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ((1 (5)) (2 (4)))))))
    (())
    |}] ;
  let p, msgs = step p 5 (Answer {round= 2; value= 2; primed= true}) in
  print_state p msgs ;
  [%expect
    {|
    ((Proposer
     ((lastOffer (((round 3) (value 2) (primed true)))) (answers ())
      (config ((node_id 0) (acceptor_ids (3 4 5)) (quorum_limit 2)))
      (primed_round_vals ((1 (5)) (2 (4 5)))))))
    (((3 (Offer ((round 3) (value 2) (primed true))))
     (4 (Offer ((round 3) (value 2) (primed true))))
     (5 (Offer ((round 3) (value 2) (primed true))))))
    |}]
