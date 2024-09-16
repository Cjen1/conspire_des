open Core
open Lib.Types
module ConSpireDES = Make (Lib.Conspire.ConSpire) (UniformDistribution)

let rec iter s should_continue =
  let open ConSpireDES in
  if should_continue s then
    match advance s with None -> s | Some s -> iter s should_continue
  else s

let merge_committed_round x y =
  match (x, y) with
  | None, None ->
      None
  | Some x, None | None, Some x ->
      Some x
  | Some (r1, v1), Some (r2, v2) ->
      assert ([%equal: int list] v1 v2) ;
      Some (min r1 r2, v1)

let get_committed_round s =
  let open ConSpireDES in
  Map.fold s.nodes ~init:None ~f:(fun ~key:_ ~data acc ->
      match data with
      | Acceptor _ ->
          acc
      | Proposer p ->
          merge_committed_round acc p.committed )

let run deterministic =
  let latency_seed : UniformDistribution.t =
    if deterministic then UniformDistribution.init
    else UniformDistribution.init_nondeterministic ()
  in
  let init_states =
    let open Lib.Conspire.ConSpire in
    let base_config =
      { node_id= -1
      ; acceptor_ids= [4; 5; 6; 7]
      ; quorum_limit= 3
      ; recovery_quorum= 3 }
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
    let open Lib.Conspire.ConSpire in
    List.init 4 ~f:(fun i ->
        (0., ConSpireDES.{src= -1; dst= i; content= Value i}) )
  in
  let s = ConSpireDES.init latency_seed init_states init_msgs in
  let p s = not (Option.is_some @@ get_committed_round s) in
  iter s p

let () =
  let n = 1_000_000 in
  let print_run () =
    let res = run false in
    let commit_round, _ = get_committed_round res |> Option.value_exn in
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
