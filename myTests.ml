open Runner
open Expr
open Printf
open OUnit2

(* Fill in `myTestList` with your own tests. There are two ways to add a test:
 *
 * (1) By adding the code of the program as a string. In this case, add an entry
 *     of this form in `myTestList`:
 *
 *     t <test_name> <program_code> <result>
 *
 * (2) By adding a test inside the 'input/' folder and adding an entry for it
 *     in `myTestList`. The entry in this case should be:
 *
 *     t_file <test_name> <file_name> <result>
 *     
 *     Where name is the name of the file inside 'input/' with the extension
 *     ".ana". For example:
 *
 *     t_file "myTest" "mytest.ana" "6";
 *)

let t_i name program expected args = name>::test_run program name expected args
let t name program expected = name>::test_run program name expected []
let terr_i name program expected args = name>::test_err program name expected args
let t_err name program expected = name>::test_err program name expected []
let t_parse name program expected =
  name>::(fun _ -> assert_equal expected (Runner.parse_string_full program));;
let boa_max = string_of_int(int_of_float(2.**62.) - 1);;

let boa_over = string_of_int(int_of_float(2.**62.) );;

let boa_min = string_of_int(-int_of_float(2.**62.));;


let boa_max_1 = string_of_int(int_of_float(2.**62.) - 2);;

let boa_min_1 = string_of_int(-int_of_float(2.**62.) + 1);;
  
let myTestList =
  [ (* Fill in your tests here: *)
  t "def_test_01" "(def even (n : Num) : Bool(if (== n 0) true (odd (- n 1))))" "6";
  t "true_test" "true" "true";

  t "false_test" "false" "false";

  t "simple_num" "6" "6";

  t "add1_test" "(add1 6)" "7";

  t "add_test" "(+ 2 6)" "8";

  t "add_test_nested" "(+ 2 (+ 1 5))" "8";

  t "sub_test" "(- 8 6)" "2";

  t "sub_test_nested" "(- 8 (- 6 4))" "6";

  t "mul_test" "(* 8 2)" "16";

  t "mul_test_nested" "(* 8 (* 3 2))" "48";



  t "lt_test_f" "(< 8 2)" "false";

  t "lt_test_t" "(< 1 2)" "true";

  t "lt_test_t2" "(< 6 21)" "true";

  t "lt_test_eq" "(< 1 1)" "false";

  t "lt_test_eq1" "(< 2 2)" "false";

  t "lt_test_eq2" "(< 3 3)" "false";

  t "lt_test_2" "(< 2 1)" "false";



  t "gt_test_t" "(> 3 2)" "true";

  t "gt_test_f" "(> 1 2)" "false";

  t "gt_test_f2" "(> 1 1)" "false";



  t "eq_test_f" "(== 1 2)" "false";

  t "eq_test_f1" "(== 3 2)" "false";

  t "eq_test_t" "(== 2 2)" "true";


  t "if_test1" "(if (== 7 7) 7 8)" "7";

  t "if_test2" "(if (== 8 7) 7 8)" "8";      

  t "if_test3" "(if (== 2 (+ 1 2)) 7 8)" "8"; 


  (* t "oflow" " 44444444444 44444444444444)" "3";

  t "oflowTimes" " 922337275807 9223372775807)" "1";  *)



  t "simpleNumPos" "1" "1";

  t "simpleNumNeg" "-2" "-2";

  t "simpleAdd1" "(add1 1)" "2";

  t "simpleSub1" "(sub1 1)" "0";

  t "simpleAddOp" "(+ 2 1)" "3";

  t "simpleSubOp" "(- 2 1)" "1";

  t "simpleTimes" "(* 2 3)" "6";

  t "nestedArithmetic1" "(- (* 2 3) (- 5 1))" "2";

  t "nestedArithmetic2" "(- 3 (- (+ 1 2) 1))" "1";

  t "letSimple" "(let ((x 1)) (add1 x))" "2";



  t "let1" "(let ((x 1)) (add1 x))" "2";

  t "let2" "(let ((x (let ((x 1)) (add1 x)))) (add1 (let ((y 1)) (add1 (let ((y 1)) (add1 (let ((y 1)) (add1 y))))))))" "5";



  t "letSimple4" "(let ((x 1) (y 2)) (+ x y))" "3";


  (*          t "oflow_add1" ("(add1 " ^ boa_max ^ ")") boa_max; *)

  t "noflow_add1" ("(add1 " ^ boa_max_1 ^ ")") boa_max; 


  t "noflow_add" ("(+ " ^ boa_max_1 ^ " 1)") boa_max; 

  (* t "oflow_add" ("(+ " ^ boa_max_1 ^ " 2)") boa_max;  

  t "oflowTimes" " 922337275807 9223372775807)" "1"; *)

  ]
;;
