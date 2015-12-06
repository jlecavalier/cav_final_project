open Printf
open Graph
module H = Hashtbl
module Q = Queue

let assign : (int * int * bool) list ref = ref []
let decision_level : int ref = ref 0
let implications : ((int * int * bool), int list) H.t = H.create 100

(* Gets the variable name from the assignment data *)
let get_var tuple = match tuple with
  | (var,_,_) -> var

(* Gets the decision level from the assignment data *)
let get_level tuple = match tuple with
  | (_,lvl,_) -> lvl

(* Displays the satisfying assignment *)
let display_assign assign =
  let assigned_vars = List.map get_var assign in
  let p_int_list lst = List.map (fun d -> (sprintf "%d" d)) lst in
  printf "[%s]\n\n" (String.concat ", " (p_int_list assigned_vars))

(* true if the given variable is in the assignment queue *)
let in_queue assign_queue var =
  let f v = match v with
    | (v',_) -> v' in
  Q.fold (fun b v -> b || ((f v) == var)) false assign_queue

(* Given a variable, return the assignment data for that variable *)
let get_data_from_var var =
  let f tuple = match tuple with
    | (v,_,_) -> (v == var) in
  assert (List.length (List.filter f !assign) > 0);
  List.hd (List.filter f !assign)

(* checks to see if the formula is unsatisfiable before we start
   searching. Also readies the assignment queue with pure literals,
   if there are any. *)
let preprocess clauses assign_queue =
  let is_literal c = (List.length c) == 1 in
  let literals = (List.flatten (List.filter is_literal clauses)) in
  (* If a unit clause and its negation occur in the formula, then return unsat. *)
  if List.fold_left (fun b l -> (b || (List.mem (-l) literals))) false literals
  then false else begin
    (* If a literal occurs purely without its negatin, we may as well set it to
       true. We add it to the assignment queue right off the bat. *)
  	let all_vars = List.flatten clauses in
  	let pure l = not (List.mem (-l) all_vars) in
  	let pure_lits = List.filter pure all_vars in
  	let f l = Q.add (l, []) assign_queue in
  	List.iter f (List.sort_uniq Pervasives.compare (pure_lits @ literals));
  	true
  end

(* Checks whether the current assignment of truth values to variables
   satisfies the formula or not. we check this every time we are about
   to assign a new value to a variable. *)
let model_found assign_queue vars =
  let assigned_vars = List.map get_var !assign in
  (Q.is_empty assign_queue) && 
  ((List.length vars) == (List.length assigned_vars))

(* Chooses a fresh variable that does not already have an assignment.
   Either the variable or its negation is selected based on which
   one of these two occurs in the formula first. *)
let decide clauses =
  let assigned_vars = List.map abs (List.map get_var !assign) in
  let new_literal literal = not (List.mem (abs literal) assigned_vars) in
  List.hd (List.filter new_literal clauses)

(* Assigns a truth value to a variable. If the assignment queue is empty,
   we use the function decide (above) to choose a variable. Otherwise,
   we dequeue the next assignment from the queue and add the result to
   the current assignment. *)
let choose_assignment assign_queue clauses =
  if (Q.is_empty assign_queue) then begin
  	let literal = decide clauses in
  	decision_level := (succ !decision_level);
    (* Begin building implication graph early *)
    H.replace implications (literal, !decision_level, false) [];
  	assign := (!assign @ [(literal, !decision_level, false)]);
  end else begin
  	let (literal, lst) = Q.take assign_queue in
    (* Begin building implication graph early *)
    H.replace implications (literal, !decision_level, true) [];
  	assign := (!assign @ [(literal, !decision_level, true)]);
  end

(* Adds an edge to the implication graph from v to l. *)
let imp_update v l =
  let tuple = get_data_from_var v in
  if H.mem implications tuple then begin
    H.replace implications tuple ((H.find implications tuple) @ [l]);
  end else begin
    H.replace implications tuple [l];
  end

(* Given a single, thus-far-unsatisfied clause and the current 
   assignment, deduce everything we can about the assignment. *)
let deduce_clause assign_queue clause =
  let assigned_vars = List.map get_var !assign in
  (* Remove a literal from the clause if its negation is 
     currently assigned true *)
  let f cs var = List.filter (fun c -> not (c == (-var))) cs in
  let d_clause = List.fold_left f clause assigned_vars in
  (* If we have obtained a unit clause, then we are forced to
     make the literal true. *)
  if ((List.length d_clause) == 1) then begin
    let literal = List.hd d_clause in
    if (not (in_queue assign_queue literal) && not (List.mem literal assigned_vars)) then begin
      (* First, figure out the reason we were forced to make this literal true. *)
      let to_negate = List.filter (fun c -> not (c == literal)) clause in
      let negated = List.map (fun c -> (-c)) to_negate in
      (* Add the according edges to the implication graph. *)
      List.iter (fun v -> imp_update v literal) negated;
      (* Queue up the forced literal. *)
      Q.add (literal,negated) assign_queue;
    end
  end

(* Deduce as much information as we can from our current clauses and
   current assignment. If we find a conflict from these deductions,
   then we will analyze the conflict using the next few functions. *)
let deduce assign_queue clauses =
  let assigned_vars = List.map get_var !assign in
  (* There is a conflict if a variable and its negation are both assigned true. *)
  if List.fold_left (fun b l -> (b || (List.mem (-l) assigned_vars))) false assigned_vars
  then true else begin
    (* If there is no conflict in the assignment, then remove all
       the clauses that are already satisfied by the assignment
       and call the procedure deduce_clause on each of the remaining
       clauses. From this we will learn as much as we can about the
       assignment. *)
    let f cs v = List.filter (fun c -> not (List.mem v c)) cs in
    let clauses' = List.fold_left f clauses assigned_vars in
    List.iter (fun c -> (deduce_clause assign_queue c)) clauses';
    (* No conflict, so return false *)
    false
  end

(* Tells us if a variable occurs on the side of the implication
   graph on which the conflict occurs *)
let conflict_side var = List.mem (var,!decision_level,true) !assign

(* Tells us if a node of the implication graph has an edge which
   enters the conflict side. *)
let enters_c_side tuple c_side =
  List.exists (fun x -> (List.mem x c_side)) (H.find implications tuple)

(* Used as a filter during backtracking. Everything that is at or above
   the current decision level must be removed from the assignment. *)
let assign_okay tuple = match tuple with
  | (_,lvl,_) -> (lvl < !decision_level)

(* Given that a conflict has occurred, this function will split
   the implication graph into two sides: one side, called the
   conflict side, contains the conflicting variables themselves and
   everything at the decision level at which the conflict occurred,
   EXCEPT for the decision variable for that decision level.
   The other side, called the reason side, contains everything else.
   We eliminate the conflict side from the graph and use the reason
   side to generate a conflict clause, which we add to our clause
   database so that we don't make the same mistake that led to this
   conflict again. *)
let analyze_conflict clauses assign_queue =
  let assigned_vars = List.map get_var !assign in
  let (c_side, r_side_big) = List.partition conflict_side assigned_vars in
  (* to generate the conflict clause, we only need the vertices on the
     reason side which have an edge that enters the conflict side. *)
  let r_side = List.filter 
    (fun x -> (enters_c_side (get_data_from_var x) c_side))
    r_side_big in
  (* Get all the decision levels on the reason side. *)
  let lvls = List.map get_level (List.map get_data_from_var r_side) in
  (* If everything on the reason side happened at decision level zero, then
     we cannot resolve the conflict. The formula must be unsatisfiable. *)
  if List.for_all (fun x -> (x == 0)) lvls then begin
    decision_level := -1;
    []
  end else begin
    (* Get the maximum decision level on the reason side that ISN'T the decision
       level at which the conflict occurred. Essentially, this is the last known
       'safe' decision level, where no conflict had yet occurred. *)
    let lvls' = List.filter (fun x -> not (x == !decision_level)) lvls in
    let lvls'' = List.rev (List.sort Pervasives.compare lvls') in
    let blevel = if ((List.length lvls'') == 0) then 0 else List.hd lvls'' in
    decision_level := blevel;
    (* Back up the assignment to the appropriate decision level *)
    assign := (List.filter assign_okay !assign);
    (* Use the reason side to generate the conflict clause. The conflict clause
       will serve as learned information which guarantees that we will not make
       the same decisions that produced the conflict we just resolved. *)
    let conflict_clause = List.map (fun x -> (-x)) r_side in
    (* Add the conflict clause to the clause database. *)
    clauses @ [conflict_clause]
  end

(* sat tells us whether the clauses are satisfiable or not. *)
let sat clauses =
  (* Initialize the clause database *)
  let working_clauses = ref clauses in
  (* Initialize the assignment queue. *)
  let assign_queue = Q.create () in
  (* If the preprocessing tells us the formula is
     unsatisfiable, then we better return unsat. *)
  let pre = preprocess !working_clauses assign_queue in
  if pre then begin
  	let vars = List.sort_uniq Pervasives.compare
  	  (List.map abs (List.flatten !working_clauses)) in
    (* maybe_sat tells us whether we can still possibly satisfy the assignment. *)
    let maybe_sat = ref true in
    (* Continue to assign variables and resolve conflicts until we find a model or
       find out that the formula cannot possibly be satisfied. *)
  	while ((not (model_found assign_queue vars)) && !maybe_sat) do
  	  choose_assignment assign_queue (List.flatten !working_clauses);
      (* Keep deducing information about the clauses and current assignment until
         we either find out that the formula cannot possibly be satisfied or we
         find a conflict. *)
      while (!maybe_sat && (deduce assign_queue !working_clauses)) do
        (* Analyze the conflict and update the clause database accordingly. *)
        working_clauses := analyze_conflict !working_clauses assign_queue;
        (* Clear the assignment queue before next assignments are made *)
        Q.clear assign_queue;
        (* Restart the implication graph. *)
        H.reset implications;
        (* Add unharmful information to the implication graph. *)
        List.iter (fun x -> (H.replace implications x [])) !assign;
        (* If we were forced to back up behind decision level 0, then the
           formula cannot possibly be satisfied. *)
        if (!decision_level < 0) then begin
          maybe_sat := false;
        end
      done
  	done;
    (* If the formula is satisfiable, display the satisfying assignment. *)
    let _ = if (!maybe_sat) then begin
      printf "\nSATISFIABLE\n\n";
      printf "Satisfying assignment:\n\n";
      display_assign !assign;
    end in
    (* Reset the assignment, decision level, and
       impication graph, in case the user specified more
       than one problem. *)
    assign := [];
    decision_level := 0;
    H.reset implications;
    !maybe_sat;
  end else false