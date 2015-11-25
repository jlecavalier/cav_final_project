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

let sat clauses =
  let assign_queue = Q.create () in
  let pre = preprocess clauses assign_queue in
  if pre then begin
  	let vars = List.sort_uniq Pervasives.compare
  	  (List.map abs (List.flatten clauses)) in
  	while (not (model_found assign_queue vars)) do
  	  printf "Infinite loop\n";
  	done;
    true
  end else false