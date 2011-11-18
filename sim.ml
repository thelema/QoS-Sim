open Batteries
open Printf

let sim_rate = 1_000_000 (* simulation ticks are each 1 us *)

module Packet = struct
  let rec cdf_pick x = function
    | [] -> assert false
    | (p,y)::_ when x <= p -> y
    | _::t -> cdf_pick x t
  
  let cdf_rand cdf = cdf_pick (Random.float 1.0) cdf
  let cdf_of_pdf pdf = 
    let sum = List.fold_left (fun acc (p,_) -> acc +. p) 0.0 pdf in
    let pdf_norm = List.map (fun (p,v) -> p /. sum, v) pdf in
    let _, rev_cdf = 
      let acc_f (psum, cdf) (p,v) = let q = psum +. p in (q, (q, v)::cdf) in
      List.fold_left acc_f (0.,[]) pdf_norm 
    in
    List.rev rev_cdf
  let pdf_of_cdf cdf =
    let _, rev_pdf = 
      let acc_f (last, pdf) (p,v) = (p, (p-.last, v)::pdf) in
      List.fold_left acc_f (0., []) cdf 
    in
    List.rev rev_pdf
  let expect pdf = List.fold_left (fun acc (p,v) -> acc +. p *. float v) 0. pdf

  (* avg packet size: 643.1*)
  let gen_cdf = [0.4,64; 0.55,100; 0.6,300; 0.65,1350; 0.75,1450; 1.0,1500]
  let expect_gen = expect (pdf_of_cdf gen_cdf)
  let gen_size () = cdf_rand gen_cdf
  let small_cdf = cdf_of_pdf [0.4,64; 0.15, 100; 0.05,300]
  let large_cdf = cdf_of_pdf [0.05,1350; 0.1, 1450; 0.25, 1500]

  let cdf_100 = [1.0,100]
  let cdf_1000 = [1.0,1000]

end

let qmax = 64_000 (* 64KB queue size *)

module HTB = struct

  let tick_interval = 0.001 (* seconds *)
  let tick_interval_sim = int_of_float (float sim_rate *. tick_interval)
  let tick_per_sec = int_of_float (1. /. tick_interval)
  let burst_time_sim = 5 * tick_interval_sim

  type htb = {ar: int; cr: int; (* the rate as number of bytes per tick *)
	      prio: int; level: int; quantum: int; 
	      mutable parent: htb option; children: htb array;
	      rate_max: int; mutable rate_tokens: int; 
	      ceil_max: int; mutable ceil_tokens: int;
	      mutable arrived: int; mutable rate: int; 
	      mutable queue_max: int; 
	      mutable waiting: int Queue.t; mutable waiting_bytes: int;
	      mutable past_rates : (string,int) Map.t list; mutable dropped: int;
	     }

  let print oc b = 
    fprintf oc "rate:%d rt: %d ct: %d queue: %a wb:%d dropped:%d" 
      b.rate b.rate_tokens b.ceil_tokens (Queue.print Int.print ~sep:",") b.waiting b.waiting_bytes b.dropped

  let make ?(children=[||]) ?parent ?(prio=3) ~qmax (ar, cr) = 
    let lev = if Array.length children = 0 then 0 
      else Array.fold_left (fun acc c -> max acc c.level) 0 children in
    let rate_max = ar * burst_time_sim / sim_rate in
    let ceil_max = cr * burst_time_sim / sim_rate in
    {ar=ar / tick_interval_sim; cr=cr / tick_interval_sim; 
     prio=prio; level=lev; quantum=1500;
     rate = 0; arrived=0;
     parent=parent; children=children; 
     rate_max=rate_max; ceil_max=ceil_max; 
     rate_tokens=0; ceil_tokens=0;
     queue_max = qmax ; waiting=Queue.create (); waiting_bytes = 0;
     past_rates = []; dropped=0}

  let make_flat ~qmax ~top_rate ~top_ceil ~child_params = 
    let children = Array.map (make ~qmax) child_params in
    (* Don't need any queueing at the parent *)
    let parent = make ~children ~qmax:0 (top_rate, top_ceil) in
    Array.iter (fun b -> b.parent <- Some parent) children;
    children

  let total_waiting htb = Queue.fold (+) 0 htb.waiting

  let enqueue htb n = 
    if htb.waiting_bytes + n < htb.queue_max then 
      (Queue.push n htb.waiting; htb.waiting_bytes <- htb.waiting_bytes + n)
    else
      htb.dropped <- htb.dropped + n

  let rec take_tokens n b = 
    b.rate_tokens <- b.rate_tokens - n;
    b.ceil_tokens <- b.ceil_tokens - n;
    b.rate <- b.rate + n;
    match b.parent with None -> () | Some b -> take_tokens n b

  let act_bytes htb n = 
    htb.arrived <- htb.arrived + n;
    if htb.ceil_tokens < n then (* must wait; enqueue *)
      enqueue htb n
    else if htb.rate_tokens < n then (* borrow tokens *)
      match htb.parent with 
	| None -> (* cannot borrow - enqueue? *) assert false (*enqueue htb n*)
	| Some p -> 
	  let den,avail = Array.fold_left (fun (d,a as acc) c -> 
	    if c != htb && c.rate > c.ar && c.rate < c.cr then 
	      (d + c.quantum,c::a) else acc) (0,[]) p.children in
	  let bc = if den = 0 then 0 else htb.quantum * p.rate / den in
(*	  printf "Pkt: %d rt:%d Borrowing: den:%d bc:%d\n%!" n htb.rate_tokens den bc; *)
	  List.iter (fun c -> c.rate_tokens <- c.rate_tokens - bc) avail;
	  p.rate_tokens <- p.rate_tokens - bc;
	  htb.rate_tokens <- htb.rate_tokens + bc;
	  if htb.rate_tokens < n then 
	    enqueue htb n
	  else	    
	    take_tokens n htb
    else ( (* ok to send *)
      take_tokens n htb
    )

(*  let act_bytes htb n = 
    printf "Pre: %a\n" print htb;
    act_bytes htb n;
    printf "Post: %a\n" print htb
*)

  let tick htb = 
    (*printf "rt_in: %d cl_in: %d\n" htb.rate_tokens htb.ceil_tokens;*)
    htb.rate_tokens <- min htb.rate_max (htb.rate_tokens + htb.ar); 
    htb.ceil_tokens <- min htb.ceil_max (htb.ceil_tokens + htb.cr);
    (*printf "rt_out: %d cl_out: %d\n" htb.rate_tokens htb.ceil_tokens;*)
    let wb_last = ref (-1) in
    while not (Queue.is_empty htb.waiting) (* there's something in the queue *)
      && !wb_last <> htb.waiting_bytes (* we didn't just re-enqueue that last packet *) do
      let n = Queue.take htb.waiting in
      wb_last := htb.waiting_bytes;
      (* correct arrived figure to not include this re-processed
	 packet *)
      htb.arrived <- htb.arrived - n; 
      htb.waiting_bytes <- htb.waiting_bytes - n;
      act_bytes htb n
    done;
    let now_stats = ["arrived", htb.arrived; "rate", htb.rate; "waiting", htb.waiting_bytes; "dropped", htb.dropped; "rate_tok", htb.rate_tokens; "ceil_tok", htb.ceil_tokens] |> List.enum |> Map.of_enum in
    htb.past_rates <- now_stats :: htb.past_rates;
    htb.rate <- 0; htb.dropped <- 0; htb.arrived <- 0

end

module PrioQueue = struct (* TODO: use splay tree *)
  type priority = int
  type 'a queue = Empty | Node of priority * 'a * 'a queue * 'a queue
  let empty = Empty
  let rec insert queue prio elt =
    match queue with
      | Empty -> Node(prio, elt, Empty, Empty)
      | Node(p, e, left, right) ->
        if prio <= p
        then Node(prio, elt, insert right p e, left)
        else Node(p, e, insert right prio elt, left)
  exception Queue_is_empty
  let rec remove_top = function
    | Empty -> raise Queue_is_empty
    | Node(prio, elt, left, Empty) -> left
    | Node(prio, elt, Empty, right) -> right
    | Node(prio, elt, (Node(lprio, lelt, _, _) as left),
           (Node(rprio, relt, _, _) as right)) ->
      if lprio <= rprio
      then Node(lprio, lelt, remove_top left, right)
      else Node(rprio, relt, left, remove_top right)
  let extract = function
    | Empty -> raise Queue_is_empty
    | Node(prio, elt, _, _) as queue -> (prio, elt, remove_top queue)
end

type event = E of int * (int -> event list)

module Equeue = struct
  let empty () = ref PrioQueue.empty

  let is_empty eq = !eq = PrioQueue.Empty

  let add eq events = eq := List.fold_left (fun acc (E(p,e)) -> PrioQueue.insert acc p e) !eq events
  let take eq = let (p,e,q) = PrioQueue.extract !eq in eq := q; (p,e)

end

module Sim = struct

  let total_rate = 10_000_000 (* 10 Mbps *)
  let n_cpus = 10
  let sim_time = 0.1 (* sec *)
  let t_max = int_of_float (sim_time *. float sim_rate) (* sim_time in sim_rate units *) 

(* generates per-cpu htbs *)
  let htb_gen_many splits = 
    let p_rate = total_rate / n_cpus in
    let p_splits = Array.map (fun (a,c) -> int_of_float(float total_rate *. a)/n_cpus, 
                                           int_of_float(float total_rate *. c)/n_cpus) splits in
    Array.init n_cpus (fun _ -> HTB.make_flat ~qmax:(qmax/n_cpus)
      ~top_rate:p_rate ~top_ceil:p_rate ~child_params:p_splits)

(* array of htbs *)
  let splits = [|0.5,0.75; 0.5,0.75|]
  let htbs = htb_gen_many splits

  let rec inject_packet gap jitter t_0 t = 
    let size = Packet.gen_size () in
    let cpu = Random.int n_cpus in
    let source = Random.int (Array.length splits) in
    HTB.act_bytes htbs.(cpu).(source) size;
    let t_next = t_0 + gap + (Random.int jitter - (jitter / 2)) in
    printf "%d: inject %d bytes cpu:%d source:%d next:%d\n" t size cpu source t_next;
    [E (t_next, inject_packet gap jitter (t_0+gap))]

  let rec packet_source rate size_cdf t = 
    let size = Packet.cdf_rand size_cdf in
    let cpu = Random.int n_cpus in
    let source = Random.int (Array.length splits) in
    HTB.act_bytes htbs.(cpu).(source) size;
    let t_next = t + size / (rate / sim_rate) in
(*    printf "%d: inject %d bytes cpu:%d source:%d next:%d\n" t size cpu source t_next;*)
    [E (t_next, packet_source rate size_cdf)]
      
  let rec tick_htb htb t =
(*    printf "%d: tick\n" t;*)
    HTB.tick htb;
    [E(t+HTB.tick_interval_sim, tick_htb htb)]

  let print_past_rates cpu_id class_id c = 
    let print_map oc m = Map.iter (fun k v -> fprintf oc "%9d\t" v) m; IO.write oc '\n' in
    List.iter (print_map stdout) (List.rev c.HTB.past_rates)

  let main () = 
    if Array.length Sys.argv < 2 then failwith "Need to specify flow bandwidth";
(*    Random.self_init();*)
    let traffic_rate = int_of_float (float_of_string Sys.argv.(1) *. 1_000_000.) in
(*    let packet_count = int_of_float (sim_time *. float traffic_rate /. Packet.expect_gen) in
    let pkt_gap = t_max / packet_count in
    printf "Traffic rate: %d Bps  * sim_time: %f / %.1f byte average packet size = %d packets\n" traffic_rate sim_time Packet.expect_gen packet_count;
  printf "Ticks between packets: %d\n" pkt_gap;*)

    let t = ref 0 in (* time in us since start of experiment *)
    let events = Equeue.empty () in
(*    Equeue.add events [E(0, inject_packet pkt_gap 50 0)];*)
    Equeue.add events [E(0, packet_source traffic_rate Packet.cdf_1000)];
    Array.iter (Array.iter (fun htb -> Equeue.add events [E(0, tick_htb htb)])) htbs;
    while !t <= t_max && not (Equeue.is_empty events) do
      let (te, event) = Equeue.take events in
      t := te;
      let next_events = event te in
      Equeue.add events next_events;
    done;

(*  Print log of statistics 
    Map.iter (fun k _ -> printf "%9s\t" k) (List.hd htbs.(0).(0).HTB.past_rates);
    printf "\n";
    Array.iteri (fun cpu_id cpu_htbs -> 
      printf "cpu_id: %d\n" cpu_id;
      Array.iteri (print_past_rates cpu_id) cpu_htbs) htbs;
*)

    let htb_sum_field field htb = List.map (Map.find field) htb.HTB.past_rates |> List.reduce (+) in
    let all_sum_field field = Array.map (Array.map (htb_sum_field field) |- Array.reduce (+)) htbs |> Array.reduce (+) in
    let dropped = all_sum_field "dropped" in
    let arrived = all_sum_field "arrived" in
    printf "Total dropped: %d = %2.1f%%\n" dropped (100. *. float dropped /. float arrived)


end

let () = Sim.main ()
