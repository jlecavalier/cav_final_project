open Printf
open Graph
module Q = Queue

let assign : (int * int * bool * int list) list ref = ref []
let implications : (int * int * bool * int list) list ref = ref []
let decision_level : int ref = ref 0

let display_assign assign =
  let assign_string tuple = match tuple with
    | (var,lvl,forced,lst) -> if forced
      then (sprintf "%d, %d, true" var lvl)
      else (sprintf "%d, %d, false" var lvl) in
  List.iter (fun t -> (print_endline (assign_string t))) assign

let in_queue assign_queue var =
  let f v = match v with
    | (v',_) -> v' in
  Q.fold (fun b v -> b || ((f v) == var)) false assign_queue

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
  let get_var tuple = match tuple with
    | (var,_,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  (Q.is_empty assign_queue) && 
  ((List.length vars) == (List.length assigned_vars))

let decide clauses =
  let get_var tuple = match tuple with
    | (var,_,_,_) -> (abs var) in
  let assigned_vars = List.map get_var !assign in
  let new_literal literal = not (List.mem (abs literal) assigned_vars) in
  List.hd (List.filter new_literal clauses)

let choose_assignment assign_queue clauses =
  if (Q.is_empty assign_queue) then begin
  	let literal = decide clauses in
  	decision_level := (succ !decision_level);
  	assign := (!assign @ [(literal, !decision_level, false, [])]);
  end else begin
  	let (literal, lst) = Q.take assign_queue in
  	assign := (!assign @ [(literal, !decision_level, true, lst)]);
  end

let deduce_clause assign_queue clause =
  let get_var tuple = match tuple with
    | (var,_,_,_) -> var in
  let assigned_vars = List.map get_var !implications in
  let f cs var = List.filter (fun c -> not (c == (-var))) cs in
  let d_clause = List.fold_left f clause assigned_vars in
  if ((List.length d_clause) == 1) then begin
    let literal = List.hd d_clause in
    if (not (in_queue assign_queue literal)) then begin
      let to_negate = List.filter (fun c -> not (c == literal)) clause in
      let negated = List.map (fun c -> (-c)) to_negate in
      Q.add (literal,negated) assign_queue;
    end
  end

let rec deduce assign_queue clauses =
  let get_var tuple = match tuple with
    | (var,_,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  print_endline "From deduce:";
  List.iter (fun v -> (printf "%d " v)) assigned_vars;
  print_endline "";
  if List.fold_left (fun b l -> (b || (List.mem (-l) assigned_vars))) false assigned_vars
  then begin
    (*assign := !implications;*)
    false
  end else begin
    let f cs v = List.filter (fun c -> not (List.mem v c)) cs in
    let clauses' = List.fold_left f clauses assigned_vars in
    List.iter (fun c -> (deduce_clause assign_queue c)) clauses';
    false
  end

let sat clauses =
  let assign_queue = Q.create () in
  let pre = preprocess clauses assign_queue in
  if pre then begin
  	let vars = List.sort_uniq Pervasives.compare
  	  (List.map abs (List.flatten clauses)) in
  	while (not (model_found assign_queue vars)) do
  	  choose_assignment assign_queue (List.flatten clauses);
      implications := !assign;
      while (deduce assign_queue clauses) do
        print_endline "Deducing";
      done;
  	done;
  	display_assign !implications;
    true
  end else false