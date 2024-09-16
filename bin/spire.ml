open Core
open Lib.Types
module SpireDES = Make (Lib.Spire.Spire) (UniformDistribution)

let rec iter s should_continue =
  let open SpireDES in
  if should_continue s then
    match advance s with None -> s | Some s -> iter s should_continue
  else s

let get_committable_round (state : SpireDES.state) lim =
  let open Lib.Spire.Spire in
  Map.fold state.nodes ~init:None ~f:(fun ~key:_ ~data acc ->
      match data with
      | Proposer {primed_round_vals; _} ->
          Map.fold primed_round_vals ~init:acc ~f:(fun ~key:round ~data:count ->
              let count = Set.length count in
              function
              | None when count >= lim ->
                  Some round
              | Some pr when count >= lim ->
                  Some (min round pr)
              | x ->
                  x )
      | Acceptor _ ->
          acc )

let run deterministic =
  let latency_seed : UniformDistribution.t =
    if deterministic then UniformDistribution.init
    else UniformDistribution.init_nondeterministic ()
  in
  let init_states =
    let open Lib.Spire.Spire in
    let base_config =
      {node_id= -1; acceptor_ids= [4; 5; 6; 7]; quorum_limit= 3}
    in
    [ (0, make_prop 0 base_config)
    ; (1, make_prop 1 base_config)
    ; (2, make_prop 2 base_config)
    ; (3, make_prop 3 base_config)
    ; (4, make_acc)
    ; (5, make_acc)
    ; (6, make_acc)
    ; (7, make_acc) ]
  in
  let init_msgs =
    let open Lib.Spire.Spire in
    List.init 4 ~f:(fun i -> (0., SpireDES.{src= -1; dst= i; content= Value i}))
  in
  let s = SpireDES.init latency_seed init_states init_msgs in
  let p s = not (Option.is_some @@ get_committable_round s 3) in
  iter s p

let () =
  let n = 1_000_000 in
  let print_run () =
    let res = run false in
    let commit_round = get_committable_round res 3 |> Option.value_exn in
    Fmt.pr "{r: %d, t: %0.4f}" commit_round res.current_time
  in
  Fmt.pr "[";
  print_run ();
  for i = 1 to n do
    if i % 10000 = 0 then
      Fmt.(pf stderr "At %d@." i);
    Fmt.pr ", ";
    print_run ()
  done;
  Fmt.pr "]"
