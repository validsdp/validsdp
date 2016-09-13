(* 
 * coqgraph - analyse and visualize file dependency information of Coq projects
 * 
 * 
 * LICENSE
 * 
 *     Copyright (C) 2013 - 2013 Hendrik Tews
 *     
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * 
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 * 
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * 
 * INSTALLATION
 * 
 *     Compile with 
 *
 *         ocamlc.opt -o coqgraph coqgraph.ml
 * 
 *     and copy coqgraph wherever you like.
 * 
 * 
 * DOCUMENTATION
 * 
 *     coqgraph converts the output of coqdep into dot format, in order
 *     to visualize the file dependencies in a Coq project.
 * 
 *     Use it as
 * 
 *          coqdep -I .  *v | coqgraph - | dot -Tpdf > dependencies.pdf
 * 
 *     You may insert tred in the pipeline before dot, in order to omit
 *     edges implied by transitivity.
 * 
 *     By default, coqgraph parses the coqdep output and outputs a dot
 *     file on stdout. The options -mark, -mark-color can be used to 
 *     set the color for certain files. The color argument of -mark-color
 *     must be a color string for dot.
 * 
 *     -root f  generates a dot file containing only the direct and 
 *              indirect dependencies of file f
 * 
 *     The other options change the operation mode of coqgraph. With any
 *     of these options it does not generate a dot file.
 * 
 *     -print-leafs
 *     -print-roots  just print the leaves or the roots
 * 
 *     -check-req    check for redundant importings
 * 
 *     -check-order files...  check if the order of files is admissible
 *                            This is useful for manually sorting the file
 *                            arguments of a coqdoc command.
 * 
 * 
 * VERSION 0.1 released on 2013-10-11
 *)


(*************************************************************************
 *
 * global variables
 *
 *************************************************************************)

let leaf_color = "aquamarine"

let root_color = "DeepSkyBlue1"

let mark_color = ref "orange"

let mark_nodes = ref []


(*************************************************************************
 *
 * general utilities
 *
 *************************************************************************)

let rec reverse_up_to a akku = function
  | [] -> akku
  | b :: rest ->
    if a = b then akku else reverse_up_to a (b :: akku) rest

let ends_with s e =
  let s_len = String.length s in
  let e_len = String.length e in
  (String.sub s (max 0 (s_len - e_len)) (min s_len e_len)) = e

let split_on_space line =
  let line_length = String.length line in
  let rec doit accu index =
    if index >= line_length then List.rev accu
    else if line.[index] = ' ' then doit accu (index + 1)
    else
      let next_space = 
	try
	  String.index_from line index ' ' 
	with
	  | Not_found -> line_length
      in
      doit ((String.sub line index (next_space - index)) :: accu) next_space
  in
  doit [] 0


(*************************************************************************
 *
 * generate dot output
 *
 *************************************************************************)


let start_dot oc =
  let o = output_string oc 
  in
  o "# Dependency graph automatically generated from coqgraph\n";
  o "# typeset with\n";
  o "#      tred x.dot | dot -Tps > x.ps\n";

  o "digraph coq_dependencies";
  o " {\n";
  o "    color=white\n";  (* border color of the invisible spacing clusters *)
  o "    node [ color = grey95, style = filled ]\n"


let output_dot_node oc color node_name =
  Printf.fprintf oc "    \"%s\" [color=%s];\n%!" node_name color

let output_dot_edge oc from_node to_node =
  Printf.fprintf oc "    \"%s\" -> \"%s\";\n%!" from_node to_node

let output_top_subgraph oc nodes =
  if nodes <> [] then begin
    let o = output_string oc 
    in
    o "    { rank=min; ";
    List.iter
      (fun node -> Printf.fprintf oc "\"%s\" " node)
      nodes;
    o ";}\n"
  end

let end_dot oc =
  output_string oc "}\n"


(*************************************************************************
 *
 * graphs
 *
 *************************************************************************)

(* An edge from A to B means B requires A *)

type node_info = {
  mutable is_leaf : bool;
  mutable is_root : bool;
}

type graph = {
  nodes : (string, node_info) Hashtbl.t;
  mutable edges : (string * string) list;
}

let graph_init () = {
  nodes = Hashtbl.create 2909;
  edges = []
}

let add_node g node_name =
  try
    ignore(Hashtbl.find g.nodes node_name)
  with
    | Not_found -> 
      Hashtbl.add g.nodes node_name 
	{ is_leaf = true;
	  is_root = true; }

let add_edge g src dest =
  add_node g src;
  add_node g dest;
  g.edges <- (src, dest) :: g.edges


let mark_inner_nodes g =
  List.iter
    (fun (src,dest) ->
      (Hashtbl.find g.nodes src).is_root <- false;
      (Hashtbl.find g.nodes dest).is_leaf <- false)
    g.edges

let get_leafs_roots g =
  let leafs = ref [] in
  let roots = ref [] in
  let isolated = ref [] in
  Hashtbl.iter
    (fun n info ->
      if info.is_leaf && info.is_root
      then isolated := n :: !isolated
      else if info.is_leaf 
      then leafs := n :: !leafs
      else if info.is_root
      then roots := n :: !roots)
    g.nodes;
  (!leafs, !roots, !isolated)


let make_direct_dependency_hash g =
  let dep_hash = Hashtbl.create 2909 in
  Hashtbl.iter
    (fun n _ -> Hashtbl.add dep_hash n (ref []))
    g.nodes;
  List.iter
    (fun (src, dest) ->
      (* dest requires src *)
      let dep_list = Hashtbl.find dep_hash dest in
      dep_list := src :: !dep_list)
    g.edges;
  dep_hash


(*************************************************************************
 *
 * print as dot
 *
 *************************************************************************)

let print_graph oc g =
  mark_inner_nodes g;
  let (leafs, roots, isolated) = get_leafs_roots g in
  start_dot oc;
  List.iter (output_dot_node oc leaf_color) isolated;
  output_top_subgraph oc isolated;
  List.iter (output_dot_node oc leaf_color) leafs;
  output_top_subgraph oc leafs;
  List.iter (output_dot_node oc root_color) roots;
  List.iter (fun (src, dest) -> output_dot_edge oc src dest) g.edges;
    List.iter (fun (color, node) -> output_dot_node oc color node) !mark_nodes;
  end_dot oc  
    
let print_leafs g =
  mark_inner_nodes g;
  let (leafs, _, isolated) = get_leafs_roots g in
  List.iter print_endline leafs;
  List.iter print_endline isolated

let print_roots g =
  mark_inner_nodes g;
  let (_, roots, isolated) = get_leafs_roots g in
  List.iter print_endline roots;
  List.iter print_endline isolated


(** returns a subgraph of [g] that contains all nodes that some node 
    in [node_list] depends on.
*)
let filter_dependencies g node_list =
  let dep_hash = Hashtbl.create 2909 in
  Hashtbl.iter
    (fun n _ -> Hashtbl.add dep_hash n (ref []))
    g.nodes;
  List.iter
    (fun (src, dest) ->
      (* dest requires src *)
      let dep_list = Hashtbl.find dep_hash dest in
      dep_list := src :: !dep_list)
    g.edges;
  let sub_nodes = Hashtbl.create 2909 in
  let rec add_dep_nodes = function
    | [] -> ()
    | [] :: rss -> add_dep_nodes rss
    | (r::rs)::rss ->
      let r_done = ref false in
      (try
	 ignore(Hashtbl.find sub_nodes r);
	 r_done := true;
       with
	 | Not_found -> ()
      );
      if !r_done 
      then add_dep_nodes (rs :: rss)
      else begin
	Hashtbl.add sub_nodes r { is_leaf = true; is_root = true; };
	add_dep_nodes (!(Hashtbl.find dep_hash r) :: rs :: rss)
      end
  in
  add_dep_nodes [node_list];
  { 
    nodes = sub_nodes;
    edges = 
      List.fold_left
	(fun akku ((src, dest) as edge) ->
	  if Hashtbl.mem sub_nodes dest
	  then begin
	    assert(Hashtbl.mem sub_nodes src);
	    edge :: akku
	  end
	  else akku)
	[]
	g.edges
  }


(*************************************************************************
 *
 * detect double require
 *
 *************************************************************************)

let check_double_require g =
  (* build the dependency hash that maps each node 
   * to its direct dependencies 
   *)
  let dep_hash = make_direct_dependency_hash g in
  (* build the transitive dependency hash that maps each node to its
   * direct and indirect dependencies. The dependency are again a
   * hash that maps the name of the dependee to the path to
   * that dependee.
   *)
  let trans_dep_hash = Hashtbl.create 2909 in
  let rec fill_trans_dep path node =
    if List.mem node path then begin
      Printf.eprintf "Error: detected dependency cycle\n  %s\n"
	(String.concat " -> " (reverse_up_to node [] path));
      exit 1;
    end;
    let path = node :: path in
    if not (Hashtbl.mem trans_dep_hash node) then begin
      List.iter (fill_trans_dep path) !(Hashtbl.find dep_hash node);
      let dependee_hash = Hashtbl.create 2909 in
      List.iter
	(fun dependee ->
	  Hashtbl.iter
	    (fun idep path ->
	      (* idep is a direct or indirect dependee of dependee
	       * and path is the path to it
	       *)
	      if not (Hashtbl.mem dependee_hash idep) 
	      then
		Hashtbl.add dependee_hash idep (dependee :: path))
	    (Hashtbl.find trans_dep_hash dependee)
	)
	!(Hashtbl.find dep_hash node);
      (* now all the direct and indirect dependees of each dependee 
       * of node are in dependee_hash. Need to add now the direct 
       * dependees of node with an empty path.
       *)
      List.iter
	(fun dependee ->
	  let other_path_opt =
	    try Some (Hashtbl.find dependee_hash dependee)
	    with Not_found -> None
	  in
	  match other_path_opt with
	    | Some other_path ->
	      Printf.printf 
		"%s: superfluous require for %s\n  imported already via %s\n"
		node dependee
		(String.concat " -> " other_path)
	    | None -> 
	      Hashtbl.add dependee_hash dependee []
	)
	!(Hashtbl.find dep_hash node);
      Hashtbl.add trans_dep_hash node dependee_hash
    end
  in
  Hashtbl.iter (fun node _ -> fill_trans_dep [] node) g.nodes


(*************************************************************************
 *
 * check ordering
 *
 *************************************************************************)

let check_order g order =
  let dep_hash = make_direct_dependency_hash g in
  let visited = Hashtbl.create 2909 in
  let check_and_mark m =
    if Hashtbl.mem visited m then begin
      Printf.eprintf "Order error!\nDuplicate %s\n" m;
      exit 1
    end;
    let deps = 
      try !(Hashtbl.find dep_hash m)
      with
	| Not_found ->
	  Printf.eprintf "Unknown module %s\n" m;
	  exit 2
    in
    let missing = 
      List.filter (fun d -> not (Hashtbl.mem visited d)) deps 
    in
    if missing = []        
    then
      Hashtbl.add visited m ()
    else begin
      Printf.printf "Order error!\n%s depends on %s\n"
	m (String.concat " " missing);
      exit 1
    end
  in
  List.iter check_and_mark order;
  print_endline "Order is OK"


(*************************************************************************
 *
 * parse coqdep files
 *
 *************************************************************************)

let dependency_edge g from_src to_node =
  let from_node =
    if ends_with from_src ".vo" 
    then String.sub from_src 0 (String.length from_src - 3)
    else from_src
  in
  add_edge g from_node to_node


let rec split_dependencies target = function
  | [] -> (target, [])
  | goal :: rest ->
    if ends_with goal ":"
    then (target, rest)
    else split_dependencies target rest

let rec split_target_dependencies = function
  | [] -> (None, [])
  | goal :: rest ->
    if ends_with goal ".vo:" 
    then (Some (String.sub goal 0 (String.length goal - 1)), rest)
    else if ends_with goal ".vo"
    then split_dependencies (Some goal) rest
    else if ends_with goal ":"
    then (None, [])
    else split_target_dependencies rest

let parse_dependency_line g line =
  let items = split_on_space line in
  let (target, dependencies) = split_target_dependencies items in
  match target with 
    | Some target -> 
      if ends_with target ".vo"
      then
	begin
	  let target_name = String.sub target 0 (String.length target - 3) in 
	  let target_src = target_name ^ ".v" in
	  add_node g target_name;
	  List.iter
	    (fun dependency ->
	      if dependency <> target_src then
		dependency_edge g dependency target_name)
	    dependencies
	end
      else
	Printf.eprintf "Ignore line with target %s\n" target
    | None -> ()

let parse_coq_depend g file =
  let ic = if file = "-" then stdin else open_in file in
  try
    while true do
      parse_dependency_line g (input_line ic)
    done
  with
    | End_of_file -> 
      if file <> "-" then close_in ic;
      ()


(*************************************************************************
 *
 * main / options
 *
 *************************************************************************)


let files = ref []

let print_leafs_flag = ref false
let print_roots_flag = ref false
let subgraph_roots = ref []
let check_req_flag = ref false
let check_order_list = ref []

let anon_fun f = 
  files := f :: !files

let usage_msg = "Usage: coqgraph [options] files..."

let options = Arg.align [
  ("-print-leafs", Arg.Set print_leafs_flag,
   " only print leafs");
  ("-print-roots", Arg.Set print_roots_flag,
   " only print roots");
  ("-mark", 
   Arg.String(fun n -> mark_nodes := (!mark_color, n) :: !mark_nodes),
   "n mark node n with special color (accumulates)");
  ("-mark-color", Arg.String(fun c -> mark_color := c),
   "c use color c for the following marked nodes");
  ("-root", Arg.String(fun r -> subgraph_roots := r :: !subgraph_roots),
   "r generate graph for r (accumulates)");
  ("-check-req", Arg.Set check_req_flag,
   " check for superfluous requires");
  ("-check-order", 
   Arg.Rest(fun m -> check_order_list := m :: !check_order_list),
   "modules... check if the order in the list is admissible");
  ("-", Arg.Unit(fun () -> files := "-" :: !files),
   " read stdin");
]

let main() =
  Arg.parse options anon_fun usage_msg;
  let g = graph_init() in
  let oc = stdout in
  List.iter (parse_coq_depend g) !files;
  if !print_leafs_flag
  then print_leafs g
  else if !print_roots_flag
  then print_roots g
  else if !subgraph_roots <> [] 
  then print_graph oc (filter_dependencies g !subgraph_roots)
  else if !check_req_flag 
  then check_double_require g
  else if !check_order_list <> []
  then check_order g (List.rev !check_order_list)
  else print_graph oc g;
  ()
;;

Printexc.print main ()

(*** Local Variables: ***)
(*** compile-command: "ocamlc.opt -o coqgraph coqgraph.ml" ***)
(*** End: ***)
