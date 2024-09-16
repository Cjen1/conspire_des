open! Core

let fmt_sexp mach =
  let inner ppf v =
    Fmt.pf ppf "%s"
      (if mach then Sexp.to_string_mach v else Sexp.to_string_hum v)
  in
  Fmt.parens inner

type node_id = int [@@deriving sexp_of]

module type Node = sig
  type node [@@deriving sexp_of]

  type msg [@@deriving sexp_of]

  val step : node -> node_id -> msg -> node * (node_id * msg) list
end

module type Latency = sig
  type t [@@deriving sexp_of]

  val init : t

  val distribution : t -> node_id -> node_id -> float * t
end

module Make (T : Node) (L : Latency) = struct
  open T

  type 'contents message = {src: node_id; dst: node_id; content: 'contents}
  [@@deriving sexp_of]

  type state =
    { nodes: node Map.M(Int).t
    ; network: T.msg message list Map.M(Float).t
    ; current_time: float
    ; latency_seed: L.t }
  [@@deriving sexp_of]

  let send s msg src dst =
    let latency, latency_seed = L.distribution s.latency_seed src dst in
    { s with
      network=
        Map.add_multi s.network
          ~key:(s.current_time +. latency)
          ~data:{src; dst; content= msg}
    ; latency_seed }

  let advance s =
    match%bind.Option Map.min_elt s.network with
    | _, [] ->
        assert false
    | t, m :: _ ->
        let s = {s with network= Map.remove_multi s.network t} in
        let nid = m.dst in
        let n', msgs = T.step (Map.find_exn s.nodes nid) m.src m.content in
        let s = {s with nodes= Map.set s.nodes ~key:nid ~data:n'} in
        let s =
          List.fold msgs ~init:s ~f:(fun s (dst, m) -> send s m nid dst)
        in
        Some {s with current_time= t}

  let init latency_seed nodes msgs =
    { nodes= Map.of_alist_exn (module Int) nodes
    ; network= Map.of_alist_multi (module Float) msgs
    ; current_time= 0.
    ; latency_seed }
end

module ConstDistribution = struct
  type t = unit [@@deriving sexp_of]

  let init = ()

  let distribution t _src _dst = (1., t)
end

module UniformDistribution = struct
  type t = Random.State.t

  let sexp_of_t _ = Sexp.unit

  let init = Random.State.make [||]
  let init_nondeterministic () = Random.State.make_self_init ()

  let distribution t _src _dst =
    let t' = Random.State.copy t in
    (Random.State.float_range t' 0. 1., t')
end

module EchoNode = struct
  type node = int [@@deriving sexp_of]

  type msg = int [@@deriving sexp_of]

  let step node src msg = (node + msg, [(src, msg + 1)])
end

let%expect_test "Echo" =
  let open Make (EchoNode) (ConstDistribution) in
  let s =
    init
      ()
      [(0, 0); (1, 1)]
      [(0., {src= 1; dst= 0; content= 2}); (0., {src= 0; dst= 1; content= 2})]
  in
  print_s (sexp_of_state s) ;
  [%expect
    {|
    ((nodes ((0 0) (1 1)))
     (network
      ((0 (((src 1) (dst 0) (content 2)) ((src 0) (dst 1) (content 2))))))
     (current_time 0) (latency_seed ()))
    |}] ;
  let s = advance s |> Option.value_exn in
  print_s (sexp_of_state s) ;
  [%expect
    {|
    ((nodes ((0 2) (1 1)))
     (network
      ((0 (((src 0) (dst 1) (content 2)))) (1 (((src 0) (dst 1) (content 3))))))
     (current_time 0) (latency_seed ()))
    |}] ;
  let s = advance s |> Option.value_exn in
  print_s (sexp_of_state s) ;
  [%expect
    {|
    ((nodes ((0 2) (1 3)))
     (network
      ((1 (((src 1) (dst 0) (content 3)) ((src 0) (dst 1) (content 3))))))
     (current_time 0) (latency_seed ()))
    |}] ;
  let s = advance s |> Option.value_exn in
  print_s (sexp_of_state s) ;
  [%expect
    {|
    ((nodes ((0 5) (1 3)))
     (network
      ((1 (((src 0) (dst 1) (content 4)) ((src 0) (dst 1) (content 3))))))
     (current_time 1) (latency_seed ()))
    |}]
