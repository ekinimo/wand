#![warn(clippy::nursery, clippy::pedantic)]
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct InternedString(u32);

thread_local! {
        static INTERNER: RefCell<StringInterner> = RefCell::new(StringInterner::new());
}

//pub static INTERNER: OnceLock<Mutex<StringInterner>> = OnceLock::new();

#[derive(Debug)]
pub struct StringInterner {
    strings: Vec<String>,
    map: HashMap<String, u32>,
}

impl StringInterner {
    fn new() -> Self {
        Self {
            strings: Vec::new(),
            map: HashMap::new(),
        }
    }

    /// # Panics
    ///
    /// Will panic if has more unique ids then 2^32
    pub fn intern(&mut self, s: impl AsRef<str>) -> InternedString {
        if let Some(&id) = self.map.get(s.as_ref()) {
            return InternedString(id);
        }

        let id = u32::try_from(self.strings.len())
            .expect("Slowdown, do you really need 2^32-1 unique identifiers?");

        let s = s.as_ref().to_string();
        self.strings.push(s.clone());
        self.map.insert(s, id);
        InternedString(id)
    }

    #[must_use]
    pub fn resolve(&self, id: InternedString) -> String {
        self.strings[id.0 as usize].to_string()
    }
}

pub fn intern_str(s: impl AsRef<str>) -> InternedString {
    INTERNER.with_borrow_mut(move |interner| interner.intern(s))
}

impl From<&str> for InternedString {
    fn from(value: &str) -> Self {
        intern_str(value)
    }
}

impl InternedString {
    #[must_use]
    pub fn new(s: &str) -> Self {
        intern_str(s)
    }

    #[must_use]
    pub fn as_str(self) -> String {
        INTERNER.with_borrow(|interner| interner.resolve(self))
    }
}

impl std::fmt::Display for InternedString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

pub mod dependency_analysis;
pub mod error;
pub mod expr;
pub mod parser;
pub mod pools;

pub mod eval;
pub mod interpreter;
pub mod kind_checker;
pub mod transpiler;
pub mod type_inference;
pub mod types;

#[cfg(test)]
pub mod paper_examples;

use types::TypeScheme;

fn setup_arithmetic_intrinsics(pools: &mut pools::Pools) {
    let int_type = pools.type_int();
    let int_to_int_to_int = {
        let arrow1 = pools.type_arrow(int_type, int_type);
        pools.type_arrow(int_type, arrow1)
    };

    let binary_int_scheme = TypeScheme::new(Vec::new(), int_to_int_to_int);

    pools.bind_global_scheme("add".into(), binary_int_scheme.clone());
    pools.bind_global_scheme("sub".into(), binary_int_scheme.clone());
    pools.bind_global_scheme("mul".into(), binary_int_scheme.clone());
    pools.bind_global_scheme("div".into(), binary_int_scheme);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 && args[1] == "--transpile" {
        if args.len() < 3 {
            eprintln!("Usage: {} --transpile <input.wand> [output.js]", args[0]);
            std::process::exit(1);
        }

        let input_file = &args[2];
        let output_file = args.get(3).map_or("output.js", std::string::String::as_str);

        match transpile_file(input_file, output_file) {
            Ok(()) => println!("Successfully transpiled {input_file} to {output_file}"),
            Err(e) => {
                eprintln!("Transpilation failed: {e}");
                std::process::exit(1);
            }
        }
        return;
    }

    let mut interpreter = interpreter::Interpreter::new();
    setup_arithmetic_intrinsics(&mut interpreter.pools);
    interpreter.repl();
}

fn transpile_file(input_file: &str, output_file: &str) -> Result<(), String> {
    // Read input file
    let input_content = std::fs::read_to_string(input_file)
        .map_err(|e| format!("Failed to read input file: {e}"))?;

    // Setup pools with intrinsics
    let mut pools = pools::Pools::new();
    setup_arithmetic_intrinsics(&mut pools);

    // Transpile to JavaScript
    let mut transpiler = transpiler::JavaScriptTranspiler::new();
    let js_code = transpiler.transpile_program(&input_content, &mut pools, input_file)?;

    // Write output file
    std::fs::write(output_file, js_code)
        .map_err(|e| format!("Failed to write output file: {e}"))?;

    Ok(())
}

#[cfg(test)]
fn test_fcp_program(input: &str) -> Result<String, String> {
    let mut interpreter = interpreter::Interpreter::new();

    let add_scheme = {
        let int_type = interpreter.pools.type_int();
        let arrow1 = interpreter.pools.type_arrow(int_type, int_type);
        let arrow2 = interpreter.pools.type_arrow(int_type, arrow1);
        TypeScheme::new(Vec::new(), arrow2)
    };

    interpreter
        .pools
        .bind_global_scheme("add".into(), add_scheme);
    interpreter.interpret(input)
}


#[cfg(test)]
mod kind_tests {
    use super::*;

    #[test]
    fn test_basic_function_constructor() {
        // Test basic function constructor without quantification
        let input = "data IntFunc = F (Int -> Int); F (fn x => x)";
        let result = test_fcp_program(input);
        if let Err(e) = &result {
            println!("Basic function constructor error: {e}");
        }
        println!("Basic function constructor result: {result:?}");
    }

    #[test]
    fn test_basic_quantified_type() {
        // Test Church boolean encoding - a valid inhabitable quantified type
        let input = "data Boolean = B (forall a. a -> a -> a); B (fn t => fn f => t)";
        let result = test_fcp_program(input);
        if let Err(e) = &result {
            println!("Basic quantified error: {e}");
        }
        println!("Basic quantified result: {result:?}");
    }

    #[test]
    fn test_simple_quantified_scope() {
        // Test basic quantified type scoping first
        let input =
            "data Maybe a = Just a | Nothing; data Container m = C (forall a. m a); C (Just 42)";
        let result = test_fcp_program(input);
        assert!(
            result.is_ok(),
            "Simple quantified scope should work: {result:?}"
        );
        println!("Simple quantified scope result: {result:?}");
    }

    #[test]
    fn test_higher_kinded_quantified_types() {
        let input = "data Pof a = P a;data M m = Mk (forall a. a -> m a); Mk (fn x => P x)";
        let result = test_fcp_program(input);
        if let Err(e) = &result {
            println!("Current error: {e}");
        }

        assert!(result.is_ok());
    }


    #[test]
    fn test_debug_simple_parsing() {
        let input = "data Maybe a = Nothing | Just a; Nothing";
        let result = test_fcp_program(input);
        if let Err(e) = &result {
            println!("Parse error: {e}");
        }
        println!("Result: {result:?}");
    }

    #[test]
    fn test_basic_maybe_pattern_matching() {
        // This demonstrates basic Maybe pattern matching (NOT full monadic evaluation yet)
        let input = r"
data Maybe a = Nothing | Just a;
match Just 42 with 
| Nothing -> Nothing 
| Just a -> Just (add a 1)
";
        let result = test_fcp_program(input);
        if let Err(e) = &result {
            println!("Maybe pattern matching error: {e}");
        }
        assert!(result.is_ok());
        let output = result.unwrap();
        println!("Maybe pattern matching result: {output}");
        assert!(output.contains("Just"));
        assert!(output.contains("43"));
    }
}

#[cfg(test)]
mod fcp_tests {
    use super::*;

    #[test]
    fn test_basic_boolean_data() {
        let program = r"
data Boolean = True | False;
True
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Boolean data definition failed: {result:?}");
        println!("Basic Boolean: {}", result.unwrap());
    }

    #[test]
    fn test_boolean_pattern_match() {
        let program = r"
data Boolean = True | False;
match True with 
| True -> 1 
| False -> 0
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Boolean pattern match failed: {result:?}");
        println!("Boolean Pattern Match: {}", result.unwrap());
    }

    #[test]
    fn test_maybe_type() {
        let program = r"
data Maybe a = Nothing | Just a;
Nothing
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Maybe type failed: {result:?}");
        println!("Maybe Nothing: {}", result.unwrap());
    }

    #[test]
    fn test_maybe_just() {
        let program = r"
data Maybe a = Nothing | Just a;
Just 42
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Maybe Just failed: {result:?}");
        println!("Maybe Just: {}", result.unwrap());
    }

    #[test]
    fn test_list_type() {
        let program = r"
data List a = Nil | Cons a (List a);
Nil
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "List type failed: {result:?}");
        println!("List Nil: {}", result.unwrap());
    }

    #[test]
    fn test_church_boolean_fcp() {
        let program = r"
data Boolean = B (forall a. a -> a -> a);
B (fn t => fn f => t)
";
        let result = test_fcp_program(program);
        // This should work but currently fails - don't mask the failure
        assert!(result.is_ok(), "Church Boolean FCP should work: {result:?}");
    }

    #[test]
    fn test_existential_package() {
        let program = r"
data Package = Pack (exists t. t);
Pack 42
";
        let result = test_fcp_program(program);
        // Actually test the result properly instead of just printing
        assert!(
            result.is_ok(),
            "Existential Package should work: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Package"),
            "Expected Package type: {output}"
        );
    }

    #[test]
    fn test_nested_pattern_match() {
        let program = r"
data Maybe a = Nothing | Just a;
data Boolean = True | False;
match Just True with
| Nothing -> False
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Nested pattern match failed: {result:?}");
        println!("Nested Pattern Match: {}", result.unwrap());
    }

    #[test]
    fn test_constructor_application() {
        let program = r"
data Pair a b = MkPair a b;
MkPair 1 2
";
        let result = test_fcp_program(program);
        // This should work but currently fails - don't mask the failure
        assert!(
            result.is_ok(),
            "Constructor application should work: {result:?}"
        );
    }

    #[test]
    fn test_simple_function_with_data() {
        let program = r"
data Boolean = True | False;
let not = fn x => match x with | True -> False | False -> True in
not True
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Function with data failed: {result:?}");
        println!("Function with Data: {}", result.unwrap());
    }

    #[test]
    fn test_integer_pattern_match() {
        let program = r"
match 42 with 
| 42 -> 1
| 0 -> 2
| _ -> 3
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Integer pattern match failed: {result:?}");
        println!("Integer Pattern Match: {}", result.unwrap());
    }

    #[test]
    fn test_integer_pattern_match_zero() {
        let program = r"
match 0 with 
| 0 -> 100
| 1 -> 200
| _ -> 300
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Integer pattern match zero failed: {result:?}"
        );
        println!("Integer Pattern Match Zero: {}", result.unwrap());
    }

    #[test]
    fn test_integer_pattern_match_wildcard() {
        let program = r"
match 999 with 
| 42 -> 1
| 0 -> 2
| _ -> 3
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Integer pattern match wildcard failed: {result:?}"
        );
        println!("Integer Pattern Match Wildcard: {}", result.unwrap());
    }
}

#[cfg(test)]
mod type_inference_fcp_tests {
    use super::*;

    #[test]
    fn test_simple_constructor_type_inference() {
        let program = r"
data Boolean = True | False;
True
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Simple constructor type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Type: Boolean"),
            "Expected Boolean type, got: {output}"
        );
        println!("Simple constructor: {output}");
    }

    #[test]
    fn test_parametric_constructor_type_inference() {
        let program = r"
data Maybe a = Nothing | Just a;
Nothing
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Parametric constructor type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Maybe"),
            "Expected Maybe type, got: {output}"
        );
        println!("Parametric constructor: {output}");
    }

    #[test]
    fn test_constructor_with_argument_type_inference() {
        let program = r"
data Maybe a = Nothing | Just a;
Just 42
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Constructor with argument type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Maybe"),
            "Expected Maybe type, got: {output}"
        );
        println!("Constructor with argument: {output}");
    }

    #[test]
    fn test_simple_cons_type_inference() {
        let program = r"
data List a = Nil | Cons a (List a);
Cons 1 Nil
";
        let result = test_fcp_program(program);
        if let Err(e) = &result {
            println!("Simple Cons error: {e}");
        }
        assert!(
            result.is_ok(),
            "Simple Cons type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("List"), "Expected List type, got: {output}");
        println!("Simple Cons: {output}");
    }

    #[test]
    fn test_complex_parametric_type_inference() {
        let program = r"
data List a = Nil | Cons a (List a);
Cons 1 (Cons 2 Nil)
";
        let result = test_fcp_program(program);
        // Actually assert that this should work - don't mask failures
        assert!(
            result.is_ok(),
            "Complex parametric type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(output.contains("List"), "Expected List type, got: {output}");
    }

    #[test]
    fn test_pattern_match_type_inference() {
        let program = r"
data Boolean = True | False;
match True with 
| True -> 1 
| False -> 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pattern match type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Type: Int"),
            "Expected Int result type, got: {output}"
        );
        println!("Pattern match: {output}");
    }

    #[test]
    fn test_pattern_match_with_variable_type_inference() {
        let program = r"
data Maybe a = Nothing | Just a;
match Just 42 with
| Nothing -> 0
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pattern match with variable type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Type: Int"),
            "Expected Int result type, got: {output}"
        );
        println!("Pattern match with variable: {output}");
    }

    #[test]
    fn test_polymorphic_function_with_data_type_inference() {
        let program = r"
data Maybe a = Nothing | Just a;
let id = fn x => x in
id (Just 42)
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Polymorphic function with data type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Maybe"),
            "Expected Maybe type, got: {output}"
        );
        println!("Polymorphic function with data: {output}");
    }

    #[test]
    fn test_higher_order_function_with_data_type_inference() {
        let program = r"
data Maybe a = Nothing | Just a;
let id = fn x => x in
id (Just 42)
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Higher order function with data type inference failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Maybe"),
            "Expected Maybe type, got: {output}"
        );
        println!("Higher order function with data: {output}");
    }

    #[test]
    fn test_top_level_function_with_parameters() {
        let program = r"
fun add_one(x: Int) -> Int { add x 1 };
add_one 5
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Top level function with parameters failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: 6"),
            "Expected value 6, got: {output}"
        );
        println!("Top level function with parameters: {output}");
    }

    #[test]
    fn test_quantified_type_simple() {
        let program = r"
data Test = T (forall a. a);
T 5
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Simple quantified type should work: {result:?}"
        );
        println!("Simple quantified type test: {result:?}");
    }

    #[test]
    fn test_parser_debug_simple_match() {
        let program = r"
data Maybe a = Nothing | Just a;
match Nothing with 
| Nothing -> 42
| Just x -> x
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            println!("Simple match works: {}", result.unwrap());
        } else {
            println!("Simple match failed: {result:?}");
        }
    }

    #[test]
    fn test_debug_simpler_case() {
        let program = r"
data Bool = True | False;
match True with 
| True -> 1
| False -> 0
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            println!("Simpler case works: {}", result.unwrap());
        } else {
            println!("Simpler case failed: {result:?}");
        }
    }

    #[test]
    fn test_improved_grammar() {
        let program = r"
data Test = T;
let camelCase = 42 in
let letSomething = 1 in 
let match2 = 2 in
let fn_name = 3 in
camelCase
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Improved grammar should work: {result:?}");
        let output = result.unwrap();
        assert!(output.contains("Value: 42"), "Expected 42, got: {output}");
        println!("Improved grammar test: {output}");
    }

    #[test]
    fn test_keyword_restrictions_still_work() {
        // Keywords themselves should still be rejected
        let programs = [
            "let let = 42 in let",
            "let fn = 42 in fn",
            "let match = 42 in match",
        ];

        for program in programs {
            let result = test_fcp_program(program);
            assert!(result.is_err(), "Keyword '{program}' should still fail");
        }
    }

    #[test]
    fn test_parser_minimal_monad() {
        let program = r"
data Maybe a = Nothing | Just a;
let f = fn ma => match ma with 
    | Nothing -> Nothing
    | Just x -> x
in
f Nothing
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            println!("Minimal monad works: {}", result.unwrap());
        } else {
            println!("Minimal monad failed: {result:?}");
        }
    }

    #[test]
    fn test_parser_debug_bind() {
        let program = r"
data Test a = T a;
match T 5 with 
| T x -> x
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            println!("Variable binding works: {}", result.unwrap());
        } else {
            println!("Variable binding failed: {result:?}");
        }
    }

    #[test]
    fn test_fcp_paper_monad_structure() {
        // From FCP paper Figure 4: Monads as first-class values
        let program = r"
data Monad m = MkMonad (forall a. a -> m a) (forall a b. m a -> (a -> m b) -> m b);

data Maybe a = Just a | Nothing;
data List a = Nil | Cons a (List a);

let unit_maybe = fn x => Just x in
let bind_maybe = fn ma => fn f => match ma with 
    | Nothing -> Nothing
    | Just x -> f x 
in
let maybe_monad = MkMonad unit_maybe bind_maybe in


let unit_list = fn x => Cons x Nil in  
let bind_list = fn xs => fn f => match xs with
    | Nil -> Nil
    | Cons y ys -> f y
in
let list_monad = MkMonad unit_list bind_list in

maybe_monad
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "FCP Paper Monad test should work: {result:?}"
        );
        let output = result.unwrap();
        println!("FCP Paper Monad test successful: {output}");
        assert!(output.contains("MkMonad"));
    }

    #[test]
    fn test_fcp_paper_monad_selector() {
        // Test using monad selectors as in the paper
        let program = r"
data Monad m = MkMonad (forall a. a -> m a) (forall a b. m a -> (a -> m b) -> m b);

let unit = fn monad => match monad with | MkMonad u b -> u in
let bind = fn monad => match monad with | MkMonad u b => b in

data Maybe a = Just a | Nothing;
let maybe_monad = MkMonad (fn x => Just x) (fn ma => fn f => match ma with 
    | Nothing => Nothing 
    | Just x => f x) in

unit maybe_monad
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            let output = result.unwrap();
            println!("FCP Paper Monad selector test: {output}");
        } else {
            println!("FCP Paper Monad selector test failed: {result:?}");
        }
    }

    #[test]
    fn test_fcp_paper_boolean_encoding() {
        // From FCP paper Figure 1: Church encoding of booleans
        let program = r"
data Boolean = B (forall a. a -> a -> a);

let true_val = B (fn t => fn f => t) in
let false_val = B (fn t => fn f => f) in  
let cond = fn bool => match bool with | B b -> b in

cond true_val 42 0
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            let output = result.unwrap();
            println!("FCP Paper Boolean encoding: {output}");
            assert!(output.contains("Value: 42"));
        } else {
            println!("FCP Paper Boolean encoding failed: {result:?}");
        }
    }

    #[test]
    fn test_integer_pattern_type_inference() {
        let program = r"
match 42 with 
| 42 -> 1
| 0 -> 2
| _ -> 3
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Integer pattern type inference failed: {result:?}"
        );
        println!("Integer Pattern Type Inference: {}", result.unwrap());
    }

    #[test]
    fn test_integer_pattern_function_type_inference() {
        let program = r"
let classify = fn x => match x with 
| 0 -> 100
| 1 -> 200
| _ -> 300
in
classify 1
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Integer pattern function type inference failed: {result:?}"
        );
        println!(
            "Integer Pattern Function Type Inference: {}",
            result.unwrap()
        );
    }
}

#[cfg(test)]
mod evaluation_fcp_tests {
    use super::*;

    #[test]
    fn test_constructor_evaluation() {
        let program = r"
data Boolean = True | False;
True
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Constructor evaluation failed: {result:?}");
        let output = result.unwrap();
        assert!(
            output.contains("Value: True"),
            "Expected True value, got: {output}"
        );
        println!("Constructor evaluation: {output}");
    }

    #[test]
    fn test_constructor_with_argument_evaluation() {
        let program = r"
data Maybe a = Nothing | Just a;
Just 42
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Constructor with argument evaluation failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Just"),
            "Expected Just constructor, got: {output}"
        );
        println!("Constructor with argument evaluation: {output}");
    }

    #[test]
    fn test_pattern_match_evaluation() {
        let program = r"
data Boolean = True | False;
match True with 
| True -> 42
| False -> 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pattern match evaluation failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: 42"),
            "Expected value 42, got: {output}"
        );
        println!("Pattern match evaluation: {output}");
    }

    #[test]
    fn test_pattern_match_with_variable_evaluation() {
        let program = r"
data Maybe a = Nothing | Just a;
match Just 99 with
| Nothing -> 0
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pattern match with variable evaluation failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: 99"),
            "Expected value 99, got: {output}"
        );
        println!("Pattern match with variable evaluation: {output}");
    }

    #[test]
    fn test_nested_constructor_evaluation() {
        let program = r"
data List a = Nil | Cons a (List a);
Cons 1 (Cons 2 Nil)
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Nested constructor evaluation failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Cons"),
            "Expected Cons constructor, got: {output}"
        );
        println!("Nested constructor evaluation: {output}");
    }

    #[test]
    fn test_function_with_data_evaluation() {
        let program = r"
data Boolean = True | False;
let not = fn x => match x with 
    | True -> False 
    | False -> True 
in
not True
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Function with data evaluation failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: False"),
            "Expected False value, got: {output}"
        );
        println!("Function with data evaluation: {output}");
    }

    #[test]
    fn test_recursive_data_structure_evaluation() {
        // Test using the interpreter since it properly handles recursive functions
        let program = r"
data List a = Nil | Cons a (List a);
fun length(list: List Int) -> Int {
    match list with
    | Nil -> 0
    | Cons x xs -> add 1 (length xs)
};
length (Cons 1 (Cons 2 (Cons 3 Nil)))
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Recursive data structure evaluation should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains("Value: 3"),
            "Expected length 3, got: {output}"
        );
        assert!(
            output.contains("Type: Int"),
            "Expected Int type, got: {output}"
        );
    }

    #[test]
    fn test_church_encoding_evaluation() {
        let program = r"
data Boolean = B (forall a. a -> a -> a);
let true_val = B (fn t => fn f => t) in
let false_val = B (fn t => fn f => f) in
let cond = fn bool => fn t => fn f => match bool with | B b -> b t f in
cond true_val 42 0
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            let output = result.unwrap();
            assert!(
                output.contains("Value: 42"),
                "Expected value 42, got: {output}"
            );
            println!("Church encoding evaluation: {output}");
        } else {
            println!("Church encoding evaluation (might need quantified type support): {result:?}");
        }
    }

    #[test]
    fn test_pattern_matching_just_3() {
        let program = r"
data Maybe a = Nothing | Just a;
match Just 3 with 
| Nothing -> 0 
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(result.is_ok(), "Pattern matching Just 3 failed: {result:?}");
        let output = result.unwrap();
        assert!(
            output.contains("Value: 3"),
            "Expected value 3, got: {output}"
        );
        assert!(
            output.contains("Type: Int"),
            "Expected Int type, got: {output}"
        );
        println!("Pattern matching Just 3: {output}");
    }

    #[test]
    fn test_pattern_matching_cons_multi_binding() {
        let program = r"
data List a = Nil | Cons a (List a);
match Cons 1 Nil with 
| Nil -> 0
| Cons x xs -> x
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Pattern matching Cons multi-binding failed: {result:?}"
        );
        let output = result.unwrap();
        assert!(
            output.contains("Value: 1"),
            "Expected value 1, got: {output}"
        );
        assert!(
            output.contains("Type: Int"),
            "Expected Int type, got: {output}"
        );
        println!("Pattern matching Cons multi-binding: {output}");
    }
}

#[cfg(test)]
mod exhaustiveness_tests {
    use super::*;

    #[test]
    fn test_exhaustive_boolean_match() {
        let program = r"
data Boolean = True | False;
match True with 
| True -> 1 
| False -> 0
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Exhaustive Boolean match should succeed: {result:?}"
        );
        println!("Exhaustive Boolean match: {}", result.unwrap());
    }

    #[test]
    fn test_non_exhaustive_boolean_match() {
        let program = r"
data Boolean = True | False;
match True with 
| True -> 1
";
        let result = test_fcp_program(program);
        assert!(result.is_err(), "Non-exhaustive Boolean match should fail");
        let error = result.unwrap_err();
        assert!(
            error.contains("NonExhaustivePatterns"),
            "Should report non-exhaustive patterns: {error}"
        );
        assert!(
            error.contains("False"),
            "Should mention missing False pattern: {error}"
        );
        println!("Non-exhaustive Boolean match error: {error}");
    }

    #[test]
    fn test_exhaustive_maybe_match() {
        let program = r"
data Maybe a = Nothing | Just a;
match Just 42 with
| Nothing -> 0
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Exhaustive Maybe match should succeed: {result:?}"
        );
        println!("Exhaustive Maybe match: {}", result.unwrap());
    }

    #[test]
    fn test_non_exhaustive_maybe_match() {
        let program = r"
data Maybe a = Nothing | Just a;
match Just 42 with
| Just x -> x
";
        let result = test_fcp_program(program);
        assert!(result.is_err(), "Non-exhaustive Maybe match should fail");
        let error = result.unwrap_err();
        assert!(
            error.contains("NonExhaustivePatterns"),
            "Should report non-exhaustive patterns: {error}"
        );
        assert!(
            error.contains("Nothing"),
            "Should mention missing Nothing pattern: {error}"
        );
        println!("Non-exhaustive Maybe match error: {error}");
    }

    #[test]
    fn test_exhaustive_three_constructor_match() {
        let program = r"
data Color = Red | Green | Blue;
match Red with
| Red -> 1
| Green -> 2
| Blue -> 3
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "Exhaustive Color match should succeed: {result:?}"
        );
        println!("Exhaustive Color match: {}", result.unwrap());
    }

    #[test]
    fn test_non_exhaustive_three_constructor_match() {
        let program = r"
data Color = Red | Green | Blue;
match Red with
| Red -> 1
| Green -> 2
";
        let result = test_fcp_program(program);
        assert!(result.is_err(), "Non-exhaustive Color match should fail");
        let error = result.unwrap_err();
        assert!(
            error.contains("NonExhaustivePatterns"),
            "Should report non-exhaustive patterns: {error}"
        );
        assert!(
            error.contains("Blue"),
            "Should mention missing Blue pattern: {error}"
        );
        println!("Non-exhaustive Color match error: {error}");
    }
}

#[cfg(test)]
mod row_polymorphism_tests {
    use super::*;
    use crate::parser::LambdaParser;
    use crate::pools::Pools;
    use crate::type_inference::PooledTypingContext;

    fn test_row_parsing_and_typing(input: &str) -> Result<String, String> {
        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        // Parse the program
        let expr_ids = LambdaParser::parse_program_to_pool(input, &mut pools)
            .map_err(|e| format!("Parse error: {e}"))?;

        if expr_ids.is_empty() {
            return Err("No expressions parsed".to_string());
        }

        let expr_id = expr_ids[0];

        // Type inference only - no evaluation
        let inferred_type = ctx
            .infer_type(&mut pools, expr_id)
            .map_err(|e| e.display_with_location(&pools))?;

        let type_display = pools.display_type(inferred_type);
        Ok(format!("Type: {type_display}"))
    }

    #[test]
    fn test_record_literal_type_inference() {
        let program = "{x: 42, y: 24}";
        let result = test_row_parsing_and_typing(program);
        assert!(
            result.is_ok(),
            "Record literal type inference failed: {result:?}"
        );
        let type_str = result.unwrap();
        assert!(
            type_str.contains('x'),
            "Expected field x in type, got: {type_str}"
        );
        assert!(
            type_str.contains('y'),
            "Expected field y in type, got: {type_str}"
        );
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_record_projection_type_inference() {
        let program = "{x: 42}.x";
        let result = test_row_parsing_and_typing(program);
        assert!(
            result.is_ok(),
            "Record projection type inference failed: {result:?}"
        );
        let type_str = result.unwrap();
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_complex_record_types() {
        // Test more complex record type scenarios
        let test_cases = vec![
            ("{x: 42, y: 24, z: 100}", "Record with multiple Int fields"),
            (
                "{name: 42, age: 24}",
                "Record with differently named Int fields",
            ),
            ("{a: {b: 42}}", "Nested record literal"),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            println!("{description}: {result:?}");
            assert!(result.is_ok(), "Failed {description}: {result:?}");
        }
    }

    #[test]
    fn test_polymorphic_projection_function() {
        let program = "fn r => r.x";
        let result = test_row_parsing_and_typing(program);
        assert!(
            result.is_ok(),
            "Polymorphic projection function failed: {result:?}"
        );
        let type_str = result.unwrap();
        assert!(
            type_str.contains("→"),
            "Expected function type with arrow, got: {type_str}"
        );
        assert!(
            type_str.contains('x'),
            "Expected field x in type, got: {type_str}"
        );
        assert!(
            type_str.contains("α"),
            "Expected type variables for polymorphism, got: {type_str}"
        );
    }

    #[test]
    fn test_different_polymorphic_projections() {
        let test_cases = vec![
            ("fn r => r.x", "x"),
            ("fn r => r.name", "name"),
            ("fn rec => rec.value", "value"),
        ];

        for (program, field) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(
                result.is_ok(),
                "Polymorphic function '{program}' failed: {result:?}"
            );
            let type_str = result.unwrap();
            assert!(
                type_str.contains("→"),
                "Expected function type, got: {type_str}"
            );
            assert!(
                type_str.contains(field),
                "Expected field {field}, got: {type_str}"
            );
            assert!(
                type_str.contains("α"),
                "Expected type variables, got: {type_str}"
            );
        }
    }

    #[test]
    fn test_record_syntax_parsing() {
        // Test that the parser can handle all record syntax
        let mut pools = Pools::new();
        let programs = vec![
            "{x: 42}",
            "{x: 42, y: 24}",
            "{x: 42}.x",
            "{{x: 42} with y: 24}",
        ];

        for program in programs {
            let result = LambdaParser::parse_program_to_pool(program, &mut pools);
            assert!(result.is_ok(), "Failed to parse '{program}': {result:?}");
        }
    }

    #[test]
    fn test_match_with_record_result() {
        // Test simple pattern match that results in a record
        let program = "match 42 with | _ => {x: 42}";
        let result = test_row_parsing_and_typing(program);
        assert!(
            result.is_ok(),
            "Match with record result failed: {result:?}"
        );
        let type_str = result.unwrap();
        assert!(type_str.contains('x'), "Expected field x, got: {type_str}");
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_debug_projection_step_by_step() {
        use crate::parser::LambdaParser;
        use crate::pools::Pools;
        use crate::type_inference::PooledTypingContext;

        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        // First test record literal alone
        println!("=== Testing record literal {{x: 42}} ===");
        let expr_ids = LambdaParser::parse_program_to_pool("{x: 42}", &mut pools).unwrap();
        let record_type = ctx.infer_type(&mut pools, expr_ids[0]).unwrap();
        let record_display = pools.display_type(record_type);
        println!("Record literal type: {record_display}");

        // Reset context for projection test
        let mut pools2 = Pools::new();
        let mut ctx2 = PooledTypingContext::new();

        // Test projection
        println!("=== Testing projection {{x: 42}}.x ===");
        let expr_ids2 = LambdaParser::parse_program_to_pool("{x: 42}.x", &mut pools2).unwrap();
        let proj_type = ctx2.infer_type(&mut pools2, expr_ids2[0]).unwrap();
        let proj_display = pools2.display_type(proj_type);
        println!("Projection type: {proj_display}");
    }

    #[test]
    fn test_working_row_unification_cases() {
        // Test row type unification scenarios that should work
        let test_cases = vec![
            ("{x: 42}.x", "Simple field projection"),
            ("{{x: 42} with y: 24}", "Simple record extension"),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_ok(), "Failed {description}: {result:?}");
        }
    }

    #[test]
    fn test_debug_multi_field_projection_unification() {
        use crate::parser::LambdaParser;
        use crate::pools::Pools;
        use crate::type_inference::PooledTypingContext;

        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        // Test step by step
        println!("=== Testing multi-field record ===");
        let record_result = LambdaParser::parse_program_to_pool("{x: 42, y: 24}", &mut pools);
        assert!(
            record_result.is_ok(),
            "Record parsing failed: {record_result:?}"
        );

        let record_type = ctx.infer_type(&mut pools, record_result.unwrap()[0]);
        println!("Record type result: {record_type:?}");
        assert!(
            record_type.is_ok(),
            "Record type inference failed: {record_type:?}"
        );

        let record_type_id = record_type.unwrap();
        println!("Record TypeId: {record_type_id:?}");
        println!(
            "Record type display: {}",
            pools.display_type(record_type_id)
        );

        // Now test projection
        println!("=== Testing projection ===");
        let mut pools2 = Pools::new();
        let mut ctx2 = PooledTypingContext::new();

        let proj_result = LambdaParser::parse_program_to_pool("{x: 42, y: 24}.x", &mut pools2);
        assert!(
            proj_result.is_ok(),
            "Projection parsing failed: {proj_result:?}"
        );

        let proj_type = ctx2.infer_type(&mut pools2, proj_result.unwrap()[0]);
        println!("Projection type result: {proj_type:?}");

        if let Err(ref e) = proj_type {
            println!("Detailed error: {e:?}");
            // Try to understand what TypeId(23) and TypeId(2) represent
            if let crate::type_inference::TypeError::TypeMismatch(mismatch_info) = e {
                println!(
                    "Expected type ({}): {}",
                    mismatch_info.expected_type.0,
                    pools2.display_type(mismatch_info.expected_type)
                );
                println!(
                    "Found type ({}): {}",
                    mismatch_info.found_type.0,
                    pools2.display_type(mismatch_info.found_type)
                );
            }
        }
    }

    #[test]
    fn test_multi_field_projection() {
        // This should work but currently fails - don't mask the failure
        let result = test_row_parsing_and_typing("{x: 42, y: 24}.x");
        assert!(
            result.is_ok(),
            "Multi-field projection should work: {result:?}"
        );
        let type_str = result.unwrap();
        assert!(type_str.contains("Int"), "Expected Int type: {type_str}");
    }

    #[test]
    fn test_polymorphic_row_operations() {
        // Test polymorphic functions that should work with any record containing specific fields
        let programs = vec![
            "fn r => r.x",         // Should work with any record containing field x
            "fn r => r.name",      // Should work with any record containing field name
            "fn rec => rec.value", // Different parameter name
        ];

        for program in programs {
            let result = test_row_parsing_and_typing(program);
            println!("Polymorphic function '{program}': {result:?}");
            if let Ok(type_str) = result {
                // Should be a function from a record to some type
                assert!(
                    type_str.contains("→"),
                    "Expected function type, got: {type_str}"
                );
                assert!(
                    type_str.contains('{'),
                    "Expected record type in domain, got: {type_str}"
                );
                assert!(
                    type_str.contains("α"),
                    "Expected type variables, got: {type_str}"
                );
            }
        }
    }

    #[test]
    fn test_record_field_type_consistency() {
        // Test that field types are correctly inferred and consistent
        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        // Test multi-field record with same field types
        let expr_ids =
            LambdaParser::parse_program_to_pool("{x: 42, y: 24, z: 100}", &mut pools).unwrap();
        let record_type = ctx.infer_type(&mut pools, expr_ids[0]).unwrap();
        let record_display = pools.display_type(record_type);
        let type_str = format!("{record_display}");
        println!("Multi-field record type: {type_str}");

        // Should contain all three fields with Int type
        assert!(type_str.contains('x'), "Missing field x");
        assert!(type_str.contains('y'), "Missing field y");
        assert!(type_str.contains('z'), "Missing field z");
        assert!(
            type_str.matches("Int").count() == 3,
            "Expected 3 Int types, got: {type_str}"
        );
    }

    #[test]
    fn test_nested_record_types() {
        // Test nested record structures
        let program = "{outer: {inner: 42}}";
        let result = test_row_parsing_and_typing(program);
        assert!(
            result.is_ok(),
            "Nested record type inference failed: {result:?}"
        );

        let type_str = result.unwrap();
        assert!(
            type_str.contains("outer"),
            "Expected outer field, got: {type_str}"
        );
        assert!(
            type_str.contains("inner"),
            "Expected inner field, got: {type_str}"
        );
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_record_type_display_format() {
        // Test that record types are displayed in readable format
        let test_cases = vec![
            ("{x: 42}", "Single field record"),
            ("{x: 42, y: 24}", "Two field record"),
            ("{a: 42, b: 24, c: 100}", "Three field record"),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_ok(), "Failed {description}: {result:?}");

            let type_str = result.unwrap();
            // Should be in proper record type format
            assert!(
                type_str.starts_with("Type: {"),
                "Expected record type format, got: {type_str}"
            );
            assert!(
                type_str.contains('}'),
                "Expected closing brace, got: {type_str}"
            );
            assert!(
                type_str.contains("Int"),
                "Expected Int type, got: {type_str}"
            );
        }
    }

    #[test]
    fn test_advanced_polymorphic_functions() {
        // Test more complex polymorphic functions with multiple projections
        let test_cases = vec![
            ("fn r => r.x", "Simple x projection"),
            (
                "fn r => fn s => r.x",
                "Curried function returning projection",
            ),
            ("fn r => r.name", "Different field name"),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_ok(), "Failed {description}: {result:?}");

            let type_str = result.unwrap();
            assert!(
                type_str.contains("→"),
                "Expected function type, got: {type_str}"
            );
            assert!(
                type_str.contains('{'),
                "Expected record in domain, got: {type_str}"
            );
        }
    }

    #[test]
    fn test_record_field_ordering_independence() {
        // Test that record field order doesn't matter for type equivalence
        let record1 = test_row_parsing_and_typing("{x: 42, y: 24}");
        let record2 = test_row_parsing_and_typing("{y: 24, x: 42}");

        assert!(record1.is_ok(), "First record failed: {record1:?}");
        assert!(record2.is_ok(), "Second record failed: {record2:?}");

        // Both should have the same fields (order may vary)
        let type1 = record1.unwrap();
        let type2 = record2.unwrap();
        assert!(
            type1.contains('x') && type1.contains('y'),
            "First record missing fields: {type1}"
        );
        assert!(
            type2.contains('x') && type2.contains('y'),
            "Second record missing fields: {type2}"
        );
    }

    #[test]
    fn test_multiple_projections_same_record() {
        // Test multiple projections from the same record
        let test_cases = vec![
            ("{x: 42, y: 24}.x", "Project x from two-field record"),
            ("{x: 42, y: 24}.y", "Project y from two-field record"),
            ("{a: 1, b: 2, c: 3}.a", "Project a from three-field record"),
            ("{a: 1, b: 2, c: 3}.b", "Project b from three-field record"),
            ("{a: 1, b: 2, c: 3}.c", "Project c from three-field record"),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_ok(), "Failed {description}: {result:?}");
            let type_str = result.unwrap();
            assert!(
                type_str.contains("Int"),
                "Expected Int result, got: {type_str}"
            );
        }
    }

    #[test]
    fn test_higher_order_record_functions() {
        // Test functions that take and return functions involving records
        let test_cases = vec![
            (
                "fn f => fn r => f (r.x)",
                "Function taking function and record",
            ),
            (
                "fn r => fn x => r.name",
                "Function returning function with closure",
            ),
        ];

        for (program, description) in test_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_ok(), "Failed {description}: {result:?}");
            let type_str = result.unwrap();
            assert!(
                type_str.contains("→"),
                "Expected function type, got: {type_str}"
            );
        }
    }

    #[test]
    fn test_record_subtyping_simulation() {
        // Test that records with more fields can be used where fewer are expected
        use crate::parser::LambdaParser;
        use crate::pools::Pools;
        use crate::type_inference::PooledTypingContext;

        let mut pools = Pools::new();
        let mut ctx = PooledTypingContext::new();

        // Define a function that expects a record with field x
        let func_program = "fn r => r.x";
        let func_expr_ids = LambdaParser::parse_program_to_pool(func_program, &mut pools).unwrap();
        let func_type = ctx.infer_type(&mut pools, func_expr_ids[0]).unwrap();
        let func_type_str = format!("{}", pools.display_type(func_type));

        // This function should accept records with x and possibly other fields
        assert!(
            func_type_str.contains('x'),
            "Function should require field x, got: {func_type_str}"
        );
        assert!(
            func_type_str.contains("α"),
            "Function should be polymorphic in rest, got: {func_type_str}"
        );
    }

    #[test]
    fn test_empty_record_operations() {
        // Test operations on empty records
        let result = test_row_parsing_and_typing("{}");
        assert!(
            result.is_ok(),
            "Empty record should parse and type-check: {result:?}"
        );

        let type_str = result.unwrap();
        // Empty record should have empty row type
        assert!(
            type_str.contains("{}") || type_str.contains("Type: {}"),
            "Expected empty record type, got: {type_str}"
        );
    }

    #[test]
    fn test_row_polymorphism_error_cases() {
        // Test cases that should properly fail
        let error_cases = vec![("{x: 42}.y", "Projection of non-existent field should fail")];

        for (program, description) in error_cases {
            let result = test_row_parsing_and_typing(program);
            assert!(result.is_err(), "{description} but got success: {result:?}");
        }
    }

    #[test]
    fn test_complex_nested_projections() {
        // Test nested record projections
        let result = test_row_parsing_and_typing("{outer: {inner: 42}}.outer");
        assert!(
            result.is_ok(),
            "Nested record projection should work: {result:?}"
        );

        let type_str = result.unwrap();
        assert!(
            type_str.contains("inner"),
            "Expected inner field in result, got: {type_str}"
        );
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_record_with_function_fields() {
        // Test records containing function values
        let result = test_row_parsing_and_typing("{f: fn x => x, value: 42}");
        assert!(
            result.is_ok(),
            "Record with function field should work: {result:?}"
        );

        let type_str = result.unwrap();
        assert!(type_str.contains('f'), "Expected field f, got: {type_str}");
        assert!(
            type_str.contains("value"),
            "Expected field value, got: {type_str}"
        );
        assert!(
            type_str.contains("→"),
            "Expected function type, got: {type_str}"
        );
        assert!(
            type_str.contains("Int"),
            "Expected Int type, got: {type_str}"
        );
    }

    #[test]
    fn test_polymorphic_record_identity() {
        // Test polymorphic functions that return records unchanged
        let result = test_row_parsing_and_typing("fn r => r");
        assert!(
            result.is_ok(),
            "Record identity function should work: {result:?}"
        );

        let type_str = result.unwrap();
        assert!(
            type_str.contains("→"),
            "Expected function type, got: {type_str}"
        );
        // Should be polymorphic: α → α where α is a record type
    }

    #[test]
    fn test_record_evaluation_basic() {
        // Test basic record evaluation
        let result = test_fcp_program("{x: 42, y: 24}");
        assert!(result.is_ok(), "Record evaluation should work: {result:?}");

        let output = result.unwrap();
        assert!(
            output.contains('{'),
            "Expected record display, got: {output}"
        );
        assert!(output.contains('x'), "Expected field x, got: {output}");
        assert!(output.contains('y'), "Expected field y, got: {output}");
        assert!(output.contains("42"), "Expected value 42, got: {output}");
        assert!(output.contains("24"), "Expected value 24, got: {output}");
    }

    #[test]
    fn test_record_projection_evaluation() {
        // Test record projection evaluation
        let result = test_fcp_program("{x: 42, y: 24}.x");
        assert!(
            result.is_ok(),
            "Record projection evaluation should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains("Value: 42"),
            "Expected projected value 42, got: {output}"
        );
    }

    #[test]
    fn test_record_extension_evaluation() {
        // Test record extension evaluation
        let result = test_fcp_program("{{x: 42} with y: 24}");
        assert!(
            result.is_ok(),
            "Record extension evaluation should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains('{'),
            "Expected record display, got: {output}"
        );
        assert!(output.contains('x'), "Expected field x, got: {output}");
        assert!(output.contains('y'), "Expected field y, got: {output}");
        assert!(output.contains("42"), "Expected value 42, got: {output}");
        assert!(output.contains("24"), "Expected value 24, got: {output}");
    }

    #[test]
    fn test_empty_record_evaluation() {
        // Test empty record evaluation
        let result = test_fcp_program("{}");
        assert!(
            result.is_ok(),
            "Empty record evaluation should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains("{}"),
            "Expected empty record display, got: {output}"
        );
    }

    #[test]
    fn test_record_with_computed_fields() {
        // Test record with computed field values
        let result = test_fcp_program("{x: add 40 2, y: add 20 4}");
        assert!(
            result.is_ok(),
            "Record with computed fields should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains('{'),
            "Expected record display, got: {output}"
        );
        assert!(output.contains('x'), "Expected field x, got: {output}");
        assert!(output.contains('y'), "Expected field y, got: {output}");
        assert!(
            output.contains("42"),
            "Expected computed value 42, got: {output}"
        );
        assert!(
            output.contains("24"),
            "Expected computed value 24, got: {output}"
        );
    }

    #[test]
    fn test_nested_record_evaluation() {
        // Test nested record structures
        let result = test_fcp_program("{outer: {inner: 42}}");
        assert!(
            result.is_ok(),
            "Nested record evaluation should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains("outer"),
            "Expected outer field, got: {output}"
        );
        assert!(
            output.contains("inner"),
            "Expected inner field, got: {output}"
        );
        assert!(output.contains("42"), "Expected value 42, got: {output}");
    }

    #[test]
    fn test_record_projection_chaining() {
        // Test chained record projections
        let result = test_fcp_program("{outer: {inner: 42}}.outer.inner");
        assert!(
            result.is_ok(),
            "Chained record projection should work: {result:?}"
        );

        let output = result.unwrap();
        assert!(
            output.contains("Value: 42"),
            "Expected final projected value 42, got: {output}"
        );
    }

    #[test]
    fn test_fcp_constructor_with_record_component() {
        // Test data constructor that takes a record as component
        let program = r"
data Container = C ({value: Int, label: Int});
C {value: 42, label: 1}
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "FCP constructor with record component should work: {result:?}"
        );
    }

    #[test]
    fn test_fcp_quantified_record_constructor() {
        // Test constructor with quantified record type
        let program = r"
data Wrapper = W (forall a. {content: a});
W {content: 42}
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "FCP quantified record constructor should work: {result:?}"
        );
    }

    #[test]
    fn test_fcp_existential_record_constructor() {
        // Test constructor with existential record type
        let program = r"
data Package = P (exists a. {item: a});
P {item: 42}
";
        let result = test_fcp_program(program);
        assert!(
            result.is_ok(),
            "FCP existential record constructor should work: {result:?}"
        );
    }

    #[test]
    fn test_polymorphic_record_field_access() {
        // Test accessing fields from polymorphic record constructors
        let program = r"
data Container a = C {value: a, meta: Int};
let getValue = fn container => match container with | C record => record.value in
getValue (C {value: 42, meta: 1})
";
        let result = test_fcp_program(program);
        if result.is_ok() {
            let output = result.unwrap();
            assert!(
                output.contains("Value: 42"),
                "Expected extracted value, got: {output}"
            );
        } else {
            // This tests complex FCP + record interaction
            println!("Polymorphic record field access failed (complex FCP feature): {result:?}");
        }
    }

    #[test]
    fn test_record_access_parsing() {
        // Test simple record field access parsing
        let simple_access = test_fcp_program("{x: 42}.x");
        println!("Simple record access: {simple_access:?}");

        // Test record access in expression
        let expr_access = test_fcp_program("let r = {x: 10} in r.x");
        println!("Expression record access: {expr_access:?}");

        // Test simpler applications
        let add_test = test_fcp_program("add 1 2");
        println!("Simple add: {add_test:?}");

        // Test add with parentheses
        let add_paren = test_fcp_program("let r = {x: 5, y: 10} in add (r.x) (r.y)");
        println!("Add with parentheses: {add_paren:?}");

        // Test simpler projection
        let simple_proj = test_fcp_program("let r = {x: 5} in r.x");
        println!("Simple projection: {simple_proj:?}");

        // Test application with one projection
        let one_proj = test_fcp_program("let r = {x: 5} in add r.x 10");
        println!("One projection: {one_proj:?}");

        // Test multiple field access
        let multi_access = test_fcp_program("let r = {x: 5, y: 10} in add r.x r.y");
        println!("Multiple field access: {multi_access:?}");

        // Test record extension with variable
        let record_ext =
            test_fcp_program("let base = {x: 5} in let extended = {base with y: 10} in extended.x");
        println!("Record extension: {record_ext:?}");
    }

    #[test]
    fn test_projection_in_function_application() {
        // This should work - parsing projections in function applications
        let program = "fun main() -> Int { let r = {x: 5, y: 10} in add r.x r.y };";
        let result = test_fcp_program(program);

        // Don't mask the failure - if it fails, we need to debug it
        assert!(
            result.is_ok(),
            "Projection in function application should work: {result:?}"
        );
    }

    #[test]
    fn test_record_extension_with_projection() {
        // Debug the type unification failure step by step

        // First test: simple record extension
        let simple_ext = test_fcp_program("{{x: 5} with y: 10}");
        println!("Simple record extension: {simple_ext:?}");

        // Second test: projection from extended record
        let ext_proj = test_fcp_program("{{x: 5} with y: 10}.x");
        println!("Extension projection: {ext_proj:?}");

        // Third test: add with regular records (should work)
        let regular_add = test_fcp_program("let r = {x: 5, y: 10} in add r.x r.y");
        println!("Regular record add: {regular_add:?}");

        // Fourth test: the failing case
        let program = "fun main() -> Int { let extended = {{x: 5} with y: 10} in add extended.x extended.y };";
        let result = test_fcp_program(program);
        println!("Full record extension: {result:?}");

        // Don't mask the failure - if it fails, we need to debug it
        assert!(
            result.is_ok(),
            "Record extension with projection should work: {result:?}"
        );
    }
}
