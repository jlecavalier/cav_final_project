open Printf
open Graph
module H = Hashtbl
module Q = Queue

let assign : (int * int * bool) list ref = ref []
let decision_level : int ref = ref 0
let implications : ((int * int * bool), int list) H.t = H.create 100

let disp_imp tuple lst = match tuple with
  | (var,lvl,forced) -> begin
    printf "%d %d --> [ " var lvl;
    List.iter (fun x -> (printf "%d " x)) lst;
    printf "]\n"
  end

let get_var tuple = match tuple with
  | (var,_,_) -> var

let get_level tuple = match tuple with
  | (_,lvl,_) -> lvl

let display_assign assign =
  let assign_string tuple = match tuple with
    | (var,lvl,forced) -> if forced
      then (sprintf "%d, %d, true" var lvl)
      else (sprintf "%d, %d, false" var lvl) in
  List.iter (fun t -> (print_endline (assign_string t))) assign

let in_queue assign_queue var =
  let f v = match v with
    | (v',_) -> v' in
  Q.fold (fun b v -> b || ((f v) == var)) false assign_queue

let get_data_from_var var =
  let f tuple = match tuple with
    | (v,_,_) -> (v == var) in
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
  let assigned_vars = List.map abs (List.map get_var !assign) in
  let new_literal literal = not (List.mem (abs literal) assigned_vars) in
  List.hd (List.filter new_literal clauses)

let choose_assignment assign_queue clauses =
  if (Q.is_empty assign_queue) then begin
  	let literal = decide clauses in
  	decision_level := (succ !decision_level);
    (*printf "%d was chosen!\n" literal;*)
    H.replace implications (literal, !decision_level, false) [];
  	assign := (!assign @ [(literal, !decision_level, false)]);
  end else begin
  	let (literal, lst) = Q.take assign_queue in
    (*printf "%d was forced!\n" literal;*)
    H.replace implications (literal, !decision_level, true) [];
  	assign := (!assign @ [(literal, !decision_level, true)]);
  end

let imp_update v l =
  let tuple = get_data_from_var v in
  if H.mem implications tuple then begin
    H.replace implications tuple ((H.find implications tuple) @ [l]);
  end else begin
    H.replace implications tuple [l];
  end

let deduce_clause assign_queue clause =
  let assigned_vars = List.map get_var !assign in
  let f cs var = List.filter (fun c -> not (c == (-var))) cs in
  let d_clause = List.fold_left f clause assigned_vars in
  if ((List.length d_clause) == 1) then begin
    let literal = List.hd d_clause in
    if (not (in_queue assign_queue literal) && not (List.mem literal assigned_vars)) then begin
      let to_negate = List.filter (fun c -> not (c == literal)) clause in
      let negated = List.map (fun c -> (-c)) to_negate in
      List.iter (fun v -> imp_update v literal) negated;
      Q.add (literal,negated) assign_queue;
    end
  end

let deduce assign_queue clauses =
  let assigned_vars = List.map get_var !assign in
  if List.fold_left (fun b l -> (b || (List.mem (-l) assigned_vars))) false assigned_vars
  then begin
    (*printf "CONFLICT FOUND:\n";
    H.iter disp_imp implications;*)
    true
  end else begin
    let f cs v = List.filter (fun c -> not (List.mem v c)) cs in
    let clauses' = List.fold_left f clauses assigned_vars in
    List.iter (fun c -> (deduce_clause assign_queue c)) clauses';
    false
  end

let conflict_side var = List.mem (var,!decision_level,true) !assign

let enters_c_side tuple c_side =
  List.exists (fun x -> (List.mem x c_side)) (H.find implications tuple)

let assign_okay tuple = match tuple with
  | (_,lvl,_) -> (lvl < !decision_level)

let backup_imp blevel =
  let remove_bad_keys key v = match key with
    | (_,lvl,_) -> begin
      if (lvl >= blevel) then begin
        while H.mem implications key do
          H.remove implications key;
        done
      end
    end in
  H.iter remove_bad_keys implications

let analyze_conflict clauses assign_queue =
  let assigned_vars = List.map get_var !assign in
  let (c_side, r_side_big) = List.partition conflict_side assigned_vars in
  let r_side = List.filter 
    (fun x -> (enters_c_side (get_data_from_var x) c_side))
    r_side_big in
  let lvls = List.map get_level (List.map get_data_from_var r_side) in
  if List.for_all (fun x -> (x == 0)) lvls then begin
    (*printf "I began the triggering!\n";*)
    decision_level := -1;
    []
  end else begin
    let lvls' = List.filter (fun x -> not (x == !decision_level)) lvls in
    let lvls'' = List.rev (List.sort Pervasives.compare lvls') in
    let blevel = if ((List.length lvls'') == 0) then 0 else List.hd lvls'' in
    decision_level := blevel;
    assign := (List.filter assign_okay !assign);
    backup_imp blevel;
    let conflict_clause = List.map (fun x -> (-x)) r_side in
    (*let p_int_list lst = List.map (fun d -> (sprintf "%d" d)) lst in
    printf "Conflict clause added: %s\n" (String.concat " " (p_int_list conflict_clause));*)
    let _ = if ((List.length conflict_clause) == 1) then begin
      Q.add ((List.hd conflict_clause),[]) assign_queue;
    end in
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
      (*printf "\nChoosing assignment!\n";*)
  	  choose_assignment assign_queue (List.flatten !working_clauses);
      while (!maybe_sat && (deduce assign_queue !working_clauses)) do
        (*print_endline "before analyze";
        display_assign !assign;*)
        working_clauses := analyze_conflict !working_clauses assign_queue;
        (*print_endline "after analyze";
        display_assign !assign;*)
        (*print_endline "And here's the queue.";
        let p_int_list lst = List.map (fun d -> (sprintf "%d" d)) lst in
        let q_elt tuple = match tuple with
        | (v,lst) -> sprintf "%d [%s]" (v) (String.concat " " (p_int_list lst)) in
        Q.iter (fun x -> (printf "%s" (q_elt x); print_endline "")) assign_queue;*)
        Q.clear assign_queue;
        H.reset implications;
        List.iter (fun x -> (H.replace implications x [])) !assign;
        if (!decision_level < 0) then begin
          (*printf "I was triggered :(\n";
          printf "decision level: %d\n" !decision_level;*)
          maybe_sat := false;
        end
      done
  	done;
    let _ = if (!maybe_sat) then begin
      (*display_assign !assign;*)
    end in
    assign := [];
    decision_level := 0;
    H.reset implications;
    !maybe_sat;
  end else false