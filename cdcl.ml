open Printf
module Q = Queue

let preprocess clauses assign_queue =
  let is_literal c = (List.length c) == 1 in
  let literals = (List.flatten (List.filter is_literal clauses)) in
  if List.fold_left (fun b l -> (b || (List.mem (-l) literals))) false literals
  then false else begin
  	let f l = Q.add l assign_queue in
  	List.iter f literals;
  	true
  end

let sat clauses = 
  let assign_queue = Q.create () in
  let pre = preprocess clauses assign_queue in
  if pre then begin
    true
  end else false