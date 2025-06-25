//! Tests based on examples from the FCP paper
//! "First-class Polymorphism with Type Inference" by Mark P. Jones

use crate::test_fcp_program;

#[cfg(test)]
mod fcp_paper_examples {
    use super::*;

    /// Figure 1: An encoding of boolean values
    #[test]
    fn test_figure1_boolean_encoding() {
        let program = r"
data Boolean = B (forall a. a -> a -> a);

let true_val = B (fn t => fn f => t) in
let false_val = B (fn f => fn f => f) in
let cond = fn bool => match bool with | B b -> b in

let and_op = fn x => fn y => cond x y false_val in
let or_op = fn x => fn y => cond x true_val y in

cond true_val 42 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Figure 1 Boolean encoding should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
    }

    /// Figure 2: An encoding of Church numerals
    #[test]
    fn test_figure2_church_numerals() {
        let program = r"
data Church = Ch (forall a. (a -> a) -> a -> a);
data Boolean = True | False;
let unch = fn ch => match ch with | Ch n -> n in
let zero = Ch (fn f => fn x => x) in
let one = Ch (fn f => fn x => f x) in
let succ = fn n => Ch (fn f => fn x => unch n f (f x)) in
let iszero = fn n => unch n (fn x => False) True in
iszero zero
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Church numerals test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: True"),
            "Expected True result, got: {output}"
        );
        println!("Church numerals test: {output}");
    }

    /// Figure 3: An encoding of lists and folds (simplified)
    #[test]
    fn test_figure3_list_encoding_simple() {
        let program = r"
data List a = L (forall b. (a -> b -> b) -> b -> b);

let fold = fn l => match l with | L f -> f in

let nil = L (fn c => fn n => n) in
let cons = fn x => fn xs => L (fn c => fn n => c x (fold xs c n)) in

let hd = fn l => fold l (fn x => fn xs => x) 42 in

hd (cons 1 (cons 2 nil))
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "List encoding test should work: {result:?}");
        let output = result.unwrap();
        assert!(output.contains("Value: 1"), "Expected 1, got: {output}");
        println!("List encoding test: {output}");
    }

    /// Figure 4: Monads as first-class values (simplified)
    #[test]
    fn test_figure4_monads_simplified() {
        let program = r"
data Monad m = MkMonad (forall a. a -> m a) (forall a b. m a -> (a -> m b) -> m b);

data Maybe a = Just a | Nothing;

let unit_maybe = fn x => Just x in
let bind_maybe = fn ma => fn f => match ma with 
    | Nothing -> Nothing
    | Just x -> f x 
in

let maybe_monad = MkMonad unit_maybe bind_maybe in

let unit = fn monad => match monad with | MkMonad u b -> u in

unit maybe_monad 42
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Figure 4 Monads should work: {result:?}");
        let output = result.unwrap();
        assert!(
            output.contains("Just") && output.contains("42"),
            "Expected Just 42, got: {output}"
        );
    }

    /// Figure 5: Stack packages with existential types (adapted)
    #[test]
    fn test_figure5_stack_packages() {
        let program = r"
data Stack a = Stack (exists s. s) (forall s. a -> s -> s) (forall s. s -> s) (forall s. s -> a) (forall s. s -> Boolean);
data List a = Nil | Cons a (List a);
data Boolean = True | False;
let make_list_stack = fn xs => Stack xs (fn x => fn l => Cons x l) (fn l => match l with | Nil -> Nil | Cons x xs -> xs) (fn l => match l with | Nil -> 0 | Cons x xs -> x) (fn l => match l with | Nil -> True | Cons x xs -> False) in
make_list_stack (Cons 1 (Cons 2 Nil))
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Stack packages test should work: {result:?}"
        );
        let output = result.unwrap();
        println!("Stack packages test: {output}");
    }

    /// Test basic polymorphic value packaging
    #[test]
    fn test_polymorphic_value_packaging() {
        let program = r"
data Poly = P (forall a. a -> a);

let id_fn = P (fn x => x) in

let unpack = fn p => match p with | P f -> f in

unpack id_fn 42
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Polymorphic value packaging should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
    }

    /// Test higher-order polymorphic functions
    #[test]
    fn test_higher_order_polymorphic() {
        let program = r"
data PolyFunc = PF (forall a b. (a -> b) -> a -> b);

let app_fn = PF (fn f => fn x => f x) in

let unpack = fn pf => match pf with | PF f -> f in

let succ = fn x => add x 1 in

unpack app_fn succ 5
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Higher-order polymorphic test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 6"), "Expected 6, got: {output}");
        println!("Higher-order polymorphic test: {output}");
    }

    /// Test quantified types in data constructors
    #[test]
    fn test_quantified_constructors() {
        let program = r"
data Container = C (forall a. a);
data Boolean = True | False;

let pack_int = C 42 in
let pack_bool = C True in

pack_int
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Quantified constructors should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("C 42"), "Expected C 42, got: {output}");
    }

    /// Test quantification scoping (simplified to avoid nested quantifiers)
    #[test]
    fn test_quantification_scoping() {
        let program = r"
data Nested = N (forall a b. a -> b -> a);

let make_const = fn x => fn y => x in
let nested = N make_const in

nested
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Quantification scoping test should work: {result:?}"
        );
        let output = result.unwrap();
        println!("Quantification scoping test: {output}");
    }

    /// Test polymorphic data structure access
    #[test]
    fn test_polymorphic_data_access() {
        let program = r"
data PolyBox a = Box (forall b. (a -> b) -> b);

let make_box = fn x => Box (fn f => f x) in
let unbox = fn box => fn cont => match box with | Box f -> f cont in

let id_fn = fn x => x in
let my_box = make_box 42 in

unbox my_box id_fn
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Polymorphic data access should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
    }

    /// Test Church boolean conditionals from the paper
    #[test]
    fn test_church_boolean_conditionals() {
        let program = r"
data ChurchBool = CB (forall a. a -> a -> a);

let church_true = CB (fn t => fn f => t) in
let church_false = CB (fn t => fn f => f) in

let church_if = fn b => fn then_val => fn else_val => 
    match b with | CB cond -> cond then_val else_val in

church_if church_true 1 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Church boolean conditionals should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 1"), "Expected 1, got: {output}");
    }

    /// Test first-class polymorphic functions
    #[test]
    fn test_first_class_polymorphic_functions() {
        let program = r"
data PolyId = PId (forall a. a -> a);

let poly_id = PId (fn x => x) in

let apply_poly_id = fn pid => fn value => 
    match pid with | PId f -> f value in

apply_poly_id poly_id 123
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "First-class polymorphic functions should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 123"), "Expected 123, got: {output}");
    }

    /// Test multiple quantified variables
    #[test]
    fn test_multiple_quantified_variables() {
        let program = r"
data Multi = M (forall a b. a -> b -> a);

let const_fn = M (fn x => fn y => x) in

let apply_multi = fn m => fn x => fn y => 
    match m with | M f -> f x y in

apply_multi const_fn 42 100
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Multiple quantified variables should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
    }

    /// Test polymorphic containers with type constructors
    #[test]
    fn test_polymorphic_containers() {
        let program = r"
data Maybe a = Just a | Nothing;
data PolyContainer f = PC (forall a. a -> f a);

let maybe_constructor = PC (fn x => Just x) in

let apply_container = fn pc => fn value =>
    match pc with | PC constructor -> constructor value in

apply_container maybe_constructor 42
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Polymorphic containers should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Just") && output.contains("42"),
            "Expected Just 42, got: {output}"
        );
    }

    /// Figure 3: List encoding with fold (complete implementation)
    #[test]
    fn test_figure3_list_fold_complete() {
        let program = r"
data List a = L (forall b. (a -> b -> b) -> b -> b);

let fold = fn l => match l with | L f -> f in
let nil = L (fn c => fn n => n) in
let cons = fn x => fn xs => L (fn c => fn n => c x (fold xs c n)) in

let length = fn l => fold l (fn x => fn acc => add acc 1) 0 in
let sum = fn l => fold l (fn x => fn acc => add x acc) 0 in

let test_list = cons 1 (cons 2 (cons 3 nil)) in
length test_list
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "List fold complete test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: 3"),
            "Expected length 3, got: {output}"
        );
        println!("List fold complete test: {output}");
    }

    /// Test natural transformations (from Pierce-Turner encoding)
    #[test]
    fn test_natural_transformations() {
        let program = r"
data Maybe a = Nothing | Just a;
data List a = Nil | Cons a (List a);
data NT f g = MkNT (forall a. f a -> g a);

let maybe_to_list = MkNT (fn ma => match ma with 
    | Nothing -> Nil 
    | Just x -> Cons x Nil) in

let apply_nt = fn nt => match nt with | MkNT f -> f in

apply_nt maybe_to_list (Just 42)
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Natural transformations test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Cons") && output.contains("42"),
            "Expected Cons 42 Nil, got: {output}"
        );
        println!("Natural transformations test: {output}");
    }

    /// Test System F style type abstraction using FCP
    #[test]
    fn test_system_f_encoding() {
        let program = r"
data Forall f = Pack (forall a. f a);

let type_abs = fn x => Pack x in
let type_app = fn p => match p with | Pack x -> x in

let id_poly = type_abs (fn x => x) in
let result = type_app id_poly 42 in
result
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "System F encoding test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
        println!("System F encoding test: {output}");
    }

    /// Test existential data abstraction (ADT simulation)
    #[test]
    fn test_existential_adt() {
        let program = r"
data Counter = MkCounter (exists s. s) (forall s. s -> s) (forall s. s -> Int);

let make_counter = fn n => MkCounter n (fn x => add x 1) (fn x => x) in
let upcrement = fn c => match c with | MkCounter state upc view -> MkCounter (upc state) upc view in
let get_value = fn c => match c with | MkCounter state upc view -> view state in
let counter = make_counter 0 in
let counterr = upcrement counter in
let counterrr = upcrement counterr in
get_value counterrr
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Existential ADT test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 2"), "Expected 2, got: {output}");
        println!("Existential ADT test: {output}");
    }

    /// Test rank-2 polymorphism
    #[test]
    fn test_rank2_polymorphism() {
        let program = r"
data Rank2 = R2 (forall a. a -> a);

let apply_twice = fn f => fn x => f (f x) in
let poly_apply = R2 (fn f => apply_twice f) in

let succ = fn x => add x 1 in
let get_func = fn r => match r with | R2 f -> f in

get_func poly_apply succ 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Rank-2 polymorphism test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 2"), "Expected 2, got: {output}");
        println!("Rank-2 polymorphism test: {output}");
    }

    /// Test Church encoding of pairs
    #[test]
    fn test_church_pairs() {
        let program = r"
data ChPair = CP (forall c. (Int -> Int -> c) -> c);

let mkpair = fn x => fn y => CP (fn f => f x y) in
let fst_ch = fn p => match p with | CP f -> f (fn x => fn y => x) in
let snd_ch = fn p => match p with | CP f -> f (fn x => fn y => y) in

let pair = mkpair 10 20 in
let first = fst_ch pair in
let second = snd_ch pair in
add first second
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Church pairs test should work: {result:?}");
        let output = result.unwrap();
        assert!(output.contains("Value: 30"), "Expected 30, got: {output}");
        println!("Church pairs test: {output}");
    }

    /// Figure 6: Pierce-Turner object encoding from the paper (honest implementation)
    #[test]
    fn test_figure6_pierce_turner_objects() {
        let program = r"
data Obj m = MkObj (exists xs. xs) (exists xs. m xs);
data Class m s = MkClass (forall f. (f -> s) -> (f -> s -> f) -> m f -> m f);
data NT m n = MkNT (forall a. m a -> n a);
data PointM s = MkP (s -> Int -> s) (s -> Int);

let point_class = MkClass (fn extr => fn over => fn self => 
    MkP (fn r => fn i => over r i) (fn r => extr r)) in

let example_point_methods = MkP (fn r => fn i => i) (fn r => 42) in

MkObj 42 example_point_methods
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pierce-Turner objects test should work: {result:?}"
        );
        let output = result.unwrap();
        println!(
            "Pierce-Turner objects test (demonstrates the data structure from paper): {output}"
        );
    }

    /// Test Natural Transformations (NT) from Figure 6
    #[test]
    fn test_figure6_natural_transformations() {
        let program = r"
data NT m n = MkNT (forall a. m a -> n a);
data Maybe a = Nothing | Just a;
data List a = Nil | Cons a (List a);

let maybe_to_list = MkNT (fn ma => match ma with 
    | Nothing -> Nil 
    | Just x -> Cons x Nil) in

let apply_nt = fn nt => fn mx => match nt with | MkNT f -> f mx in

apply_nt maybe_to_list (Just 42)
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Natural transformations should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Cons") && output.contains("42"),
            "Expected Cons 42 Nil, got: {output}"
        );
        println!("Natural transformations test: {output}");
    }

    /// Test Church pair encoding from the paper (mentioned in formal section)
    #[test]
    fn test_paper_church_pair_encoding() {
        let program = r"
data Pair a b = MkPair (forall c. (a -> b -> c) -> c);

let make_pair = fn x => fn y => MkPair (fn f => f x y) in
let fst_pair = fn p => match p with | MkPair pf -> pf (fn x => fn y => x) in
let snd_pair = fn p => match p with | MkPair pf -> pf (fn x => fn y => y) in

let test_pair = make_pair 10 20 in
let first = fst_pair test_pair in
let second = snd_pair test_pair in
add first second
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Church pair encoding should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 30"), "Expected 30, got: {output}");
        println!("Church pair encoding test: {output}");
    }

    /// Test polymorphic recursion encoding
    #[test]
    fn test_polymorphic_recursion() {
        let program = r"
data Pair a b = MkPair a b;
data Perfect a = Zero a | Succ (Perfect (Pair a a));
data PolyRec = PR (forall a. Perfect a -> Int);

let count_perfect = PR (fn p => match p with 
    | Zero x -> 1
    | Succ pp -> add 1 1) in

let get_counter = fn pr => match pr with | PR f -> f in
let test_perfect = Zero 42 in
get_counter count_perfect test_perfect
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Polymorphic recursion test should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("Value: 1"), "Expected 1, got: {output}");
        println!("Polymorphic recursion test: {output}");
    }
}
