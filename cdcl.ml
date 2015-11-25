open Printf
module Q = Queue

let assign : (int * int * bool) list ref = ref []
let decision_level : int ref = ref 0

let preprocess clauses assign_queue =
  let is_literal c = (List.length c) == 1 in
  let literals = (List.flatten (List.filter is_literal clauses)) in
  if List.fold_left (fun b l -> (b || (List.mem (-l) literals))) false literals
  then false else begin
  	let all_vars = List.flatten clauses in
  	let pure l = not (List.mem (-l) all_vars) in
  	let pure_lits = List.filter pure all_vars in
  	let f l = Q.add l assign_queue in
  	List.iter f (List.sort_uniq Pervasives.compare (pure_lits @ literals));
  	true
  end

let model_found assign_queue vars =
  let get_var tuple = match tuple with
    | (var,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  (Q.is_empty assign_queue) && 
  ((List.length vars) == (List.length assigned_vars))

let decide clauses =
  let get_var tuple = match tuple with
    | (var,_,_) -> var in
  let assigned_vars = List.map get_var !assign in
  let new_literal literal = not (List.mem (abs literal) assigned_vars) in
  List.hd (List.filter new_literal clauses)

let choose_assignment assign_queue clauses =
  if (Q.is_empty assign_queue) then begin
  	let literal = decide clauses in
  	decision_level := (succ !decision_level);
  	assign := (!assign @ [(literal, !decision_level, false)]);
  end else begin
  	let literal = Q.take assign_queue in
  	assign := (!assign @ [(literal, !decision_level, true)]);
  end

let display_assign assign =
  let assign_string tuple = match tuple with
    | (var,lvl,forced) -> if forced
      then (sprintf "%d, %d, true" var lvl)
      else (sprintf "%d, %d, false" var lvl) in
  List.iter (fun t -> (print_endline (assign_string t))) assign

let sat clauses =
  let assign_queue = Q.create () in
  let pre = preprocess clauses assign_queue in
  if pre then begin
  	let vars = List.sort_uniq Pervasives.compare
  	  (List.map abs (List.flatten clauses)) in
  	while (not (model_found assign_queue vars)) do
  	  choose_assignment assign_queue (List.flatten clauses);
  	done;
  	display_assign !assign;
    true
  end else false