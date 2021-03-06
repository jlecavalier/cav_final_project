open Printf
open Cdcl

let linenum : int ref = ref 1
let results : Pervasives.out_channel = open_out "time_results.dat"

(* Extract the information from the parser into clauses *)
let rec ints_to_clauses clauses clause l =
  match l with
  | [] -> clauses
  | _ -> match (List.hd l) with
        | 0 -> begin
          if ((List.length l) == 1) then (clauses @ [clause])
       	  else ints_to_clauses (clauses @ [clause]) [] (List.tl l)
       	end
        | x -> begin
          if ((List.length l) == 1) then assert false
      	  else ints_to_clauses clauses (clause @ [x]) (List.tl l)
      	end

let check_num_variables clauses num_vars =
  let c = (List.flatten clauses) in
  let vars = List.map abs c in
  let unique_vars = List.sort_uniq Pervasives.compare vars in
  (List.length unique_vars) == num_vars

(* Verify that the user gave us the number of variables and clauses
   he/she said she would in the spec file. *)
let check_properties p c =
  let num_vars = List.nth p 0 in
  let num_clauses = List.nth p 1 in
  assert (num_vars >= 0);
  assert (num_clauses >= 0);
  (*printf "%d variables\n" num_vars;
  printf "%d clauses\n" num_clauses;*)
  assert ((List.hd (List.rev c)) == 0);
  let clauses = ints_to_clauses [] [] c in
  assert ((List.length clauses) == num_clauses);
  assert (check_num_variables clauses num_vars);
  clauses

(* Solve SAT! *)
let do_sat clauses = 
  let t = Sys.time() in
  let is_sat = Cdcl.sat clauses in
  let runtime = Sys.time() -. t in
  let runtime_string = Printf.sprintf "%f\n" runtime in
  output_string results runtime_string;
  Printf.printf "Found solution in %f seconds\n" (runtime);
  is_sat