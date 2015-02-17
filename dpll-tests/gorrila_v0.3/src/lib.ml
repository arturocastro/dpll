(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2009-2010 K. Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)

(* switch on for debug mode*)
(*let debug = true*)
let debug = false

let out_str s = print_endline s 

let system_name = "GoRRiLA v0.3"
let _= out_str ("\n--------------------- "^system_name^" ---------------------\n")

(*--------------------Signals Timers---------------*)
exception Termination_Signal
exception Time_out_real
exception Time_out_virtual

let set_sys_signals () = 
  let signal_handler signal =
    if (signal = Sys.sigint || signal = Sys.sigterm || signal = Sys.sigquit) 
    then raise Termination_Signal
    else 
      if (signal = Sys.sigalrm) 
      then raise Time_out_real
      else 
	if (signal = Sys.sigvtalrm)
	then raise Time_out_virtual
	else failwith "Unknown Signal"
  in  	  
  Sys.set_signal Sys.sigint     (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigterm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigquit    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigalrm    (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigvtalrm  (Sys.Signal_handle signal_handler)


  
let _ = set_sys_signals ()

let set_timer time_limit = 
  (if time_limit > 0. 
  then 
    let _= 
	Unix.setitimer Unix.ITIMER_REAL
	{
   	 Unix.it_interval = 0.;
   	 Unix.it_value  = time_limit;
       }  in ()
  ) 
 
let reset_timer () = 
    let _= 
	Unix.setitimer Unix.ITIMER_REAL
	{
   	 Unix.it_interval = 0.;
   	 Unix.it_value  = 0.;
       }  in ()
      

(*------------------------------*)
 

(*---------Memory control---------*)


let mem_control_init () = 
  let old_controls = Gc.get () in
  let new_controls = {old_controls with Gc.major_heap_increment= 1048576} in
  Gc.set new_controls

let _ =  mem_control_init ()

(*------------------------------*)



type 'a param = Def of 'a | Undef 

(* truncates float to n digits after . *)
let truncate_n n f = 
  let fl_n =  (10.**(float_of_int n)) in
  (float_of_int (truncate (f*.fl_n)))/.fl_n


let get_some = function 
  |Some x -> x 
  |None -> failwith "get_some: None"

(* outcome of  compare fun *)
let cequal   =  0
let cgreater =  1
let cless    = -1

let compose_12 g f x y = g (f x y)

let param_to_string el_to_string elp = 
  match elp with 
  |Def(el) -> el_to_string el 
  |Undef   -> "Undef"

(* elements and ref to elem of indexies and all others*)

let () =  Random.init(13)

(*hash function called djb2*)

let hash_sum rest num = 
  ((rest lsl 5) + rest) + num (* hash * 33 + num *)

type 'a elem = Elem of 'a | Empty_Elem
type 'a ref_elem = ('a elem) ref


(* Some regular expressions *)
let reg_expr_float =  Str.regexp "[0-9]+\\.[0-9]*" 


let xor a b = (not a = b)

let xor_list list = List.fold_left xor false list


(*-----------Intervals-------------*)

(* all bounds inclusive*)
type interval = int*int

let interval_to_string (l,r) =
  "["^(string_of_int l)^","^(string_of_int r)^"]"

let interval_to_string_p (l,r) =
  (string_of_int l)^"_"^(string_of_int r)


let parse_interval str =
  let str_list = (Str.split (Str.regexp "\\[\\|,\\|\\]") str) in
  match str_list with
  |[l_str;r_str] -> ((int_of_string l_str),(int_of_string r_str))
  |_-> failwith ("parse_interval: "^str^" is not a valid interval")

let inter_consistent (l,r) = 
  if r>= l 
  then true 
  else false 

let inter_consistent_positive (l,r) =
    (inter_consistent (l,r)) && (l>=0)

let rnd_from_inter (l,r) = 
  assert (r >= l);
  (Random.int (r-l+1))+l

type inter_float = float * float
let inter_float_to_int (f_l,f_r) = 
  (int_of_float f_l, int_of_float f_r)

(*---------itervals of types [4.,5.] or [1.5v,3.7v], or [0.5,4.v]-----------*)
(* v is also considered to be float *)
type bound_cv = 
    BConst of float
  |BVar of float 

type inter_const_var = bound_cv*bound_cv

exception Not_bound_cv
let parse_var_bound_cv str = 
  let str_list =  (Str.full_split reg_expr_float str) in
  try 
    match str_list with 
    |[Str.Delim (float_str);Str.Text ("v")] -> BVar(float_of_string float_str)
    |[Str.Delim(float_str)] -> BConst(float_of_string float_str)
    |_->raise Not_bound_cv
  with 
    Failure ("float_of_string") -> raise Not_bound_cv

let parse_inter_const_var str = 
  let str_list = (Str.split (Str.regexp "\\[\\|,\\|\\]") str) in
  try
    match str_list with 
    |[l_str;r_str] -> ((parse_var_bound_cv l_str), (parse_var_bound_cv r_str))
    |_-> 
	raise Not_bound_cv
  with Not_bound_cv -> 
    failwith ("\""^str^"\" is not a valid <interval_var>")

(* subsitutes v in the constr_var interval *)
let bound_cv_to_float v b_cv =
  match b_cv with 
  |BConst f -> f 
  |BVar f   -> v*.f

let inter_const_var_to_float v constr_var_inter =
  let (l, r) =  constr_var_inter in
 (bound_cv_to_float v l, bound_cv_to_float v r)



(*-------String Streams--------*)
 
(* string stream can be e.g. a buffer or a channel *)
type 'a string_stream = 
    {
     buff : 'a;
     add_char : char   -> unit;
     add_str  : string -> unit;
   }
   

let rnd_bool () = 
  if (Random.int 2) = 0 
  then true 
  else false

(*------Processes------------------------*)

(*--create_process_newgr forks a process in a new process group-----*)
(*--This can be used to kill the child process and all children of the child--*)
(*------ Example: 
 *   let process_id = 
 *	create_process_newgr 
 *	  (process_cmd) 
 *	  (Array.of_list args_list)
 *	  (*Unix.stdin *)
 *	  (Unix.descr_of_in_channel in_channel)
 *	  (Unix.descr_of_out_channel out_channel)
 *	(*  Unix.stderr*)
 *	  (Unix.descr_of_out_channel err_channel)
 *     let _process_status =  Unix.waitpid [] process_id in ...
 *  
 *)

(*------------From unix.ml--------------*)

(* Close file descriptor ignoring errors *)
let safe_close fd =
  try Unix.close fd with Unix.Unix_error(_,_,_) -> ()

(* Redirect stdin, stdout and stderr *)
let perform_redirections new_stdin new_stdout new_stderr =
(*  Unix.dup2 new_stdin Unix.stdin; 
  Unix.dup2 new_stdout Unix.stdout;
  Unix.dup2 new_stderr Unix.stderr
*)
  let newnewstdin = Unix.dup new_stdin in
  let newnewstdout = Unix.dup new_stdout in
  let newnewstderr = Unix.dup new_stderr in
  safe_close new_stdin;
  safe_close new_stdout;
  safe_close new_stderr;
  Unix.dup2 newnewstdin Unix.stdin; Unix.close newnewstdin;
  Unix.dup2 newnewstdout Unix.stdout; Unix.close newnewstdout;
  Unix.dup2 newnewstderr Unix.stderr; Unix.close newnewstderr


(* Create process in a new process group *)
let create_process_newgr cmd args new_stdin new_stdout new_stderr =
  match Unix.fork() with
    0 ->
      (*Unix.set_close_on_exec new_stdout;*)
      begin try
        perform_redirections new_stdin new_stdout new_stderr;
	ignore (Unix.setsid ());
       Unix.execvp cmd args	
      with _ ->
        exit 127
      end
  | id -> id



(*--------------------------------------------------------------------------------------------------*)
(* Ocaml's signal numbers to names *) 
(* Numbers can be system dependent and it is not clear they  correspond to the standad Unix numbers *)
(* Why it is not in Sys module ???*)
(*--------------------------------------------------------------------------------------------------*)


let sygnals_name_table = 
  [    
 (Sys.sigabrt, "sigabrt");
 (Sys.sigalrm, "sigalrm"); 
 (Sys.sigfpe,  "sigfpe");
 (Sys.sighup,  "sighup");
 (Sys.sigill,  "sigill");
 (Sys.sigint,  "sigint"); 
 (Sys.sigkill,  "sigkill");  
 (Sys.sigpipe,  "sigpipe");
 (Sys.sigquit,  "sigquit"); 
 (Sys.sigsegv,  "sigsegv"); 
 (Sys.sigterm,  "sigterm"); 
 (Sys.sigusr1,  "sigusr1"); 
 (Sys.sigusr2,  "sigusr2"); 
 (Sys.sigchld,  "sigchld"); 
 (Sys.sigcont,  "sigcont"); 
 (Sys.sigstop,  "sigstop"); 
 (Sys.sigtstp,  "sigtstp"); 
 (Sys.sigttin,  "sigttin"); 
 (Sys.sigttou,  "sigttou"); 
 (Sys.sigvtalrm,  "sigvtalrm"); 
 (Sys.sigprof,   "sigprof");  
  ]

let signal_to_string i = 
  try
    List.assoc i sygnals_name_table
  with 
    Not_found -> "unknown_signal"


(* "Normally_Terminated (i)" where i is the exit code *)
(* "Ubnormally_Terminated signal_name"  signa_name is according to Sys mudle *)


type termination_status = 
    Normally_Terminated of int| Ubnormally_Terminated of string


let termination_status_to_string ts = 
  match ts with 
  |Normally_Terminated   i  -> ("exit "^(string_of_int i))
  |Ubnormally_Terminated s  -> ("killed "^s)


let parse_termination_status str = 
  let str_list = (Str.split (Str.regexp " ") str) in  
  match str_list with 
  |["exit";i_str]   ->  Normally_Terminated (int_of_string i_str)
  |["killed";sig_str] ->  Ubnormally_Terminated (sig_str)
  |_-> failwith ("parse_termination_status:"^str^" unrecognised termination status")


let check_process_status process_status =
  match process_status with 
  |Unix.WEXITED   i   -> Normally_Terminated i
  |Unix.WSIGNALED i   -> Ubnormally_Terminated (signal_to_string i)
  |Unix.WSTOPPED  i   -> Ubnormally_Terminated (signal_to_string i)



(*---------------*)
(*
let check_process_status process_name process_status =
  match process_status with 
(*      The process terminated normally by exit; the argument is the return code.       *)
  |     Unix.WEXITED int  -> ()
    (*  if int = 0 then ()
      else 
        failwith (" Error "^process_name^" exit with status: "
                  ^(string_of_int int))
*)

(*      The process was killed by a signal; the argument is the signal number.  *)
  |     Unix.WSIGNALED int -> 
      failwith (" Error "^process_name^" was killed by a signal: "
                  ^(string_of_int int))
        (*      The process was stopped by a signal; the argument is the signal number. *)
  |     Unix.WSTOPPED int ->
      failwith (" Error "^process_name^" was stopped by a signal: "
                ^(string_of_int int))

*)

(*----------Global Open Child Processes--------------*)

let child_processes_list_ref = ref []

let add_child_process pid = 
  child_processes_list_ref:= pid::!child_processes_list_ref

let kill_process_group pid = 
  try                         
    (* Kill processes in process group *)
    Unix.kill (-pid) Sys.sigkill;                             
    ignore(Unix.waitpid [] pid)
  with 
    Unix.Unix_error(Unix.ESRCH, _, _) -> ()

let remove_top_child_process () = 
  match !child_processes_list_ref with 
  |[] -> ()
  |h::tl ->
      kill_process_group h;
      child_processes_list_ref:= tl

let kill_all_child_processes () = 
  List.iter kill_process_group !child_processes_list_ref




(*-----------Files---------*)

let remove_file file_name = 
  let in_channel = Unix.open_process_in ("rm -f "^file_name) in
  let _status = Unix.close_process_in in_channel in ()


let open_file_append file_name = 
  if (Sys.file_exists file_name)
  then  	
    let user_read_write_others_read = 644 in
    open_out_gen [Open_append] user_read_write_others_read file_name
  else open_out file_name 

let file_append_str file_name str =
  let channel = open_file_append file_name in
  output_string channel str;
  flush channel;
  close_out channel

(*
let is_dir_fail str = 
(*  try*)
  if Sys.is_directory str then ()
  else failwith (str^" is not a dir")
 (* with Sys_error -> failwith ("dir "^str^"does not exist")*)
*)

(*--------------------*)


let param_str_ref = ref ""
let pref_str = "------ "



let add_param_str str = 
  param_str_ref := (!param_str_ref)^pref_str^str^"\n"

let add_param_str_front str = 
   param_str_ref := pref_str^str^"\n"^(!param_str_ref)

let param_str_new_line () = 
   param_str_ref := (!param_str_ref)^"\n"


(*compose sign with function*)

let compose_sign sign f = 
  if sign then f 
  else compose_12 (~-) f




(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)

type 'a bind = int * 'a

let propagate_binding_to_list blist =
  let (b_l,list) = blist in  
  List.map (fun el -> (b_l,el)) list

(* bool operations *)
let bool_plus x y = ((x&& (not y)) || ((not x)&& y))
(*    let out_str s = Printf.fprintf stdout " %s \n" s *)


(*let out_str_debug s =
  if debug then out_str s else ()*)

    
(*let out_str_a s = Printf.fprintf stdout " %s \n" s *)

(* lexicographic comparison on pairs*)

let pair_compare_lex comp1 comp2 (x1,x2) (y1,y2) = 
  let res_comp1 = comp1 x1 y1 in
  if res_comp1=cequal then 
    let res_comp2 = comp2 x2 y2 in
      if res_comp2 = cequal then 
	cequal
      else res_comp2
  else res_comp1

(* lex combination of all compare functions in compare_fun_list*)
let rec lex_combination compare_fun_list x1 x2 = 
  match compare_fun_list with 
  | h::tl -> 
      let res = h x1 x2 in 
      if res = cequal then lex_combination tl x1 x2
      else res
  |[] -> cequal 
       



(* bound lists*)

type 'a bound_list = ('a list) bind

(*
let rec bound_list_fold_left f a (bound_list : bound_list) = 
 
 *)



(*------------------- Lists----------------------*)


(* returns list which starts with the next elem *)
(* assume that elem in l *)
(* careful if there are duplicates*)

let rec list_skip elem l = 
  match l with 
  | h::tl -> 
      if (h==elem) then tl 
      else  list_skip elem tl	
  | [] -> failwith "Lib list_skip: elem should be in l"

  

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)

let rec list_map_left f l  = 
  match l with    
  | h::tl -> let new_h = f h in 
    new_h :: (list_map_left f tl)
  | [] -> []
	

let rec list_to_string to_str_el l separator_str =
  match l with
    []->""
  | h::[] -> to_str_el h
  | h::rest -> 
      (to_str_el h)^separator_str^(list_to_string to_str_el rest separator_str)

let list_of_str_to_str str_list separator_str = 
    list_to_string (fun x->x) str_list separator_str

(* stops when f is Some(e) and returns Some(e) otherwise returns None  *)
let rec list_findf f = function 
  |h::tl -> 
      (match (f h) with 
      |Some(e)-> Some(e)
      |None -> list_findf f tl
      )
  |[] -> None



let rec list_compare_lex compare_el l1 l2 =
  match (l1,l2) with
  |((h1::tl1),(h2::tl2)) -> 
      let cmp = compare_el h1 h2 in   
      if (cmp = cequal) then
	list_compare_lex compare_el tl1 tl2
      else cmp 
 |((h::_),[]) -> cequal + 1
 |([],(h::_)) -> cequal -1
 |([],[]) -> cequal


(* in list_get_max_elements_v 
   is mainly for non-ground (not exactly) orderings
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
   Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s*)    

let rec list_is_max_elem_v compare elem list = 
  match list with 
  |h::tl -> 
(*      if ((not (h == elem)) & ((compare h elem) >= 0))       
      then false 
      else (list_is_max_elem_v compare elem tl) 
*)
      if (h == elem) || not ((compare h elem) > 0) 
      then (list_is_max_elem_v compare elem tl)
      else false  
  |[] -> true

let list_get_max_elements_v compare list = 
  let f rest elem = 
    if  list_is_max_elem_v compare elem list
    then elem::rest
    else rest 
  in List.fold_left f [] list

(* for usual orderings *)
let rec list_is_max_elem compare elem list = 
  match list with 
  |h::tl -> 
      if (compare h elem) > 0
      then false 
      else (list_is_max_elem compare elem tl)
  |[] -> true

let rec list_find_max_element compare list =
  match list with 
  |h::tl -> 
      if tl = [] 
      then h
      else
	let max_rest = list_find_max_element compare tl in
	if (compare max_rest h) > 0 
	then max_rest
	else h
  |[] -> raise Not_found

let rec list_find_max_element_p test cmp list =
  match list with 
  |h::tl -> 
      if (test h) 
      then
	(if tl = [] 
	then h
	else
	  (try 
	    let max_rest = list_find_max_element_p test cmp tl in
	    if (cmp h max_rest) > 0 
	    then h 
	    else max_rest
	  with Not_found -> h	 
	  )
	)    
      else list_find_max_element_p test cmp tl
  |[] -> raise Not_found


(*---------------removes duplicate elements from the list-----------------*)

let rec list_remove_duplicates' rest list =
  match list with 
  |h::tl -> 
      if (List.memq h rest) then 
	list_remove_duplicates' rest tl
      else 
	list_remove_duplicates' (h::rest) tl
  |[] -> rest

let list_remove_duplicates list = 
  List.rev (list_remove_duplicates' [] list) 


(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)

let rec list_remove_duplicates_ordered list = 
  match list with 
  |h1::h2::tl -> 
      if h1==h2 
      then list_remove_duplicates_ordered (h2::tl) 
      else (h1::(list_remove_duplicates (h2::tl)))
  |[h] -> [h]
  |[]   -> []


(* like List.find but for two lists in parallel*)

let rec list_find2 f l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then (h1,h2) 
      else list_find2 f tl1 tl2
  |_ -> raise Not_found

(* like list_find2 only returns (g h1 h2)  *) 

let rec list_return_g_if_f2 f g l1 l2 = 
  match (l1,l2) with
  | ((h1::tl1),(h2::tl2)) -> 
      if f h1 h2  then g h1 h2 
      else list_return_g_if_f2 f g tl1 tl2
  |_ -> raise Not_found

(* *)
let rec list_find_not_equal compare_el l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      let c = compare_el h1 h2 in 
      if  c<>cequal then c 
      else list_find_not_equal compare_el tl1 tl2
  |_ -> raise Not_found


let rec list_find_not_identical l1 l2 = 
  match (l1,l2) with
  | (h1::tl1,h2::tl2) -> 
      if  not (h1==h2) then (h1,h2) 
      else list_find_not_identical tl1 tl2
  |_ -> raise Not_found




(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f v1 v2))
 otherwise  appends (k1,v1) and (k2,v2)*)


let rec append_ass_list f ass_list_1 ass_list_2  = 
  match ass_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 ass_list_2 in 
       let new_list_2 = 
           (k1,(f v1 v2))::(List.remove_assoc k1 ass_list_2) in   
       append_ass_list f tl1 new_list_2  
     with
       Not_found -> append_ass_list f tl1 ((k1,v1)::ass_list_2)
     )
  |[] -> ass_list_2

(* number association lists *)

type ('a, 'b) ass_list = ('a*'b) list

type 'a num_ass_list =  ('a, int) ass_list




(* dangerous: old lists are changing...
 association lists on ref's

type 'a 'b ass_list = ('a*('b ref)) list

let rec append_ass_list f ass_list_1 ass_list_2  = 
  match n_list_1 with 
  |(k1,v1)::tl1 -> 
     (try 
       let v2 = List.assoc k1 n_list_2 in 
       v2 := f !v1 !v2 ;
       append_ass_list f tl1 ass_list_2  
     with
       Not_found -> (k1,v1)::n_list_2
     )
  |[] -> ass_list_2

*)


(* assume L is a list f : P(L) -> bool is anti-monotonic w.r.t inlcusion *)
(* (false<true) then  get_maximal_sublist f l = (max,rest)               *)
(* where max is a maximal (w.r.t inlcusion)                              *)
(* subset of L such that f(max) = true and rest is the rest of the list  *)

let get_maximal_sublist f list = 
  let rec get_maximal_sublist' rest sel l = 
    match l with 
    | h::tl -> 
	if (f (h::sel))
	then 
	  get_maximal_sublist' rest (h::sel) tl
	else
	  get_maximal_sublist' (h::rest) sel tl
    | [] -> (sel,rest)
  in
  get_maximal_sublist' [] [] list

(*---------strings-----------*)

(*string filled with n spaces *)
let space_str n = 
  if n>0 
  then
    (String.make n ' ')
  else " "

(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)

let space_padding_str distance str =
  let name_ln = String.length str in
  str^(space_str (distance - name_ln))


(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end



(*--------------Global Time Limits-------------------*)

(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)

exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)
let discount_time_limit  = ref Undef
let start_discount_time  = ref Undef

let assign_discount_time_limit (x:float) =   discount_time_limit := Def(x)
let assign_discount_start_time () = 
  start_discount_time := Def((Unix.gettimeofday ()))

let get_start_disc_time () = 
  match !start_discount_time with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: start_time is Undef"

let get_disc_time_limit () = 
  match !discount_time_limit with 
  |Def(t) -> t
  |Undef  -> failwith "Discount: discount_time_limit is Undef"

let check_disc_time_limit () = 
  match !discount_time_limit with
  | Def(t_limit) -> 
      if ((Unix.gettimeofday ()) -. (get_start_disc_time ())) > t_limit 
      then raise Timeout
      else ()
  |Undef -> ()
