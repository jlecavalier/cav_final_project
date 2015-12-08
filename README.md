# camlogic: a CDCL SAT solver for OCaml

# Prerequisites
NOTE: It is STRONGLY recommended that you install items 2-4 using opam, the OCaml package manager.
1. OCaml version >= 4.0.2
2. ocamlfind --> https://opam.ocaml.org/packages/ocamlfind/ocamlfind.1.5.5/
3. oasis --> http://oasis.forge.ocamlcore.org/
4. ocamllex and ocamlyacc --> http://caml.inria.fr/pub/docs/manual-ocaml-4.00/manual026.html

# How to Compile
1. Navigate to the root directory of this repository using your terminal.
2. type "./configure"
3. type "make"

# Usage
To run camlogic, you must feed the program a list of DIMACS format files. DIMACS is a format for concisely representing a formula in propositional logic, and typically come with the extension .cnf. If you want to see some example DIMACS files, please see the /specs directory. To run the program:

./main.native [files]

where [files] represents a list of files to solve.

The solver will return the following information:
1. The amount of time taken to solve the problem in seconds.
2. Whether the formula was satisfiable or not.
3. If the formula is satisfiable, you will see a satisfying assignment of truth values to variables.
4. Results about the amount of time it took to solve the problem (in seconds) are written to a file "time_results.dat" in the root directory. This is useful if you want to collect runtime data about many problems all at once.
