open Printf
open Graph
module H = Hashtbl
module Q = Queue

let assign : (int * int * bool * int list) list ref = ref []
let decision_level : int ref = ref 0
let implications : ((int * int * bool), int list) H.t = H.create 100

let get_var tuple = match tuple with
  | (var,_,_,_) -> var

let display_assign assign =
  let do_list lst = String.concat " " (List.map (fun l -> (sprintf "%d" l)) lst) in
  let assign_string tuple = match tuple with
    | (var,lvl,forced,lst) -> if forced
      then (sprintf "%d, %d, true [%s]" var lvl (do_list lst))
      else (sprintf "%d, %d, false [%s]" var lvl (do_list lst)) in
  List.iter (fun t -> (print_endline (assign_string t))) assign

let in_queue assign_queue var =
  let f v = match v with
    | (v',_) -> v' in
  Q.fold (fun b v -> b || ((f v) == var)) false assign_queue

let get_data_from_var var =
  let f tuple = match tuple with
    | (v,_,_,_) -> (v == var) in
  assert (List.length (List.filter f !assign) > 0);
  List.hd (List.filter f !assign)

let preprocess clauses assign_queue =
  let is_literal c = (List.length c) == 1 in
  let literals = (List.flatten (List.filter is_literal clauses)) in
  if List.fold_left (fun b l -> (b || (List.mem (-l) literals))) false literals
  then false else begin
  	let all_vars = List.flatten clauses in
  	let pure l = not (List.mem (-l) all_vars) in
  	let pure_lits = List.filter pure all_vars in
  	let f l = Q.add (l, []) assign_queue in
  	List.iter f (List.sort_uniq Pervasives.compare (pure_lits @ literals));
  	true
  end

let model_found assign_queue vars =
  let assigned_vars = List.map get_var !assign in
  (Q.is_empty assign_queue) && 
  ((List.length vars) == (List.length assigned_vars))

let decide clauses =
  let assigned_vars = List.map get_var !assign in
  let new_literal literal = not (List.mem (abs literal) assigned_vars) in
  List.hd (List.filter new_literal clauses)

let choose_assignment assign_queue clauses =
  if (Q.is_empty assign_queue) then begin
  	let literal = decide clauses in
  	decision_level := (succ !decision_level);
    H.replace implications (literal, !decision_level, false) [];
  	assign := (!assign @ [(literal, !decision_level, false, [])]);
  end else begin
  	let (literal, lst) = Q.take assign_queue in
    H.replace implications (literal, !decision_level, true) [];
  	assign := (!assign @ [(literal, !decision_level, true, lst)]);
  end

let deduce_clause assign_queue clause =
  let get_var tuple = match tuple with
    | (var,_,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  let f cs var = List.filter (fun c -> not (c == (-var))) cs in
  let d_clause = List.fold_left f clause assigned_vars in
  if ((List.length d_clause) == 1) then begin
    assert ((List.length d_clause) > 0);
    let literal = List.hd d_clause in
    if (not (in_queue assign_queue literal)) then begin
      let to_negate = List.filter (fun c -> not (c == literal)) clause in
      let negated = List.map (fun c -> (-c)) to_negate in
      Q.add (literal,negated) assign_queue;
    end
  end

let deduce assign_queue clauses =
  let assigned_vars = List.map get_var !assign in
  if List.fold_left (fun b l -> (b || (List.mem (-l) assigned_vars))) false assigned_vars
  then begin
    true
  end else begin
    let f cs v = List.filter (fun c -> not (List.mem v c)) cs in
    let clauses' = List.fold_left f clauses assigned_vars in
    List.iter (fun c -> (deduce_clause assign_queue c)) clauses';
    false
  end

let analyze_conflict clauses = 
  let get_var tuple = match tuple with
    | (var,_,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  let is_conflict tuple = List.mem (-(get_var tuple)) assigned_vars in
  let conflict_vars = List.filter is_conflict !assign in
  let get_causes tuple = match tuple with
    | (_,_,_,cause) -> cause in
  let causes = List.sort_uniq Pervasives.compare
    (List.flatten (List.map get_causes conflict_vars)) in
  let get_level tuple = match tuple with
    | (_,lvl,_,_) -> lvl in
  let lvls = List.map get_level (List.map get_data_from_var causes) in
  let blevel = pred (List.hd (List.sort Pervasives.compare lvls)) in
  if (blevel < 0) then begin 
    decision_level := -1;
    [] 
  end else begin
    let conflict_clause = List.map (fun v -> -v) causes in
    decision_level := blevel;
    assign := List.filter (fun t -> ((get_level t) <= blevel)) !assign;
    clauses @ [conflict_clause]
  end

let sat clauses =
  let working_clauses = ref clauses in
  let assign_queue = Q.create () in
  let pre = preprocess !working_clauses assign_queue in
  if pre then begin
  	let vars = List.sort_uniq Pervasives.compare
  	  (List.map abs (List.flatten !working_clauses)) in
    let maybe_sat = ref true in
  	while ((not (model_found assign_queue vars)) && !maybe_sat) do
  	  choose_assignment assign_queue (List.flatten !working_clauses);
      while ((deduce assign_queue !working_clauses) && !maybe_sat) do
        (*print_endline "before analyze";
        display_assign !assign;*)
        working_clauses := analyze_conflict !working_clauses;
        (*print_endline "after analyze";
        display_assign !assign;
        print_endline "And here's the queue.";
        let p_int_list lst = List.map (fun d -> (sprintf "%d" d)) lst in
        let q_elt tuple = match tuple with
        | (v,lst) -> sprintf "%d [%s]" (v) (String.concat " " (p_int_list lst)) in
        Q.iter (fun x -> (printf "%s" (q_elt x); print_endline "")) assign_queue;*)
        Q.clear assign_queue;
        if (!decision_level < 0) then begin
          maybe_sat := false;
        end
      done;
  	done;
    assign := [];
    decision_level := 0;
    !maybe_sat;
  end else false