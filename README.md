# Wand

A functional programming language implementing first-class polymorphism and row types with full inference. 
Work in progress.

## About

Wand is an experimental implementation of a functional programming language. It tries to combine first-class polymorphism (FCP) and row polymorphism.

First class polymorphism is based on the paper "First-class Polymorphism with Type Inference" by Mark P. Jones. This basically allows us to use the `forall` and `exists` quantifiers in DataConstrocturs.

Row polymophims is inspired by "Type inference for record concatenation and multiple inheritance" by Mitchell Wand. This feature is implemented in  languages like `Elm`, `purescript`.  

## Features:
- Algebraic data types with pattern matching
- Row polymorphism for extensible records
- First-class polymorphism with universal and existential quantification
- Hindley-Milner type inference extended for FCP
- Higher-kinded types 

## Usage

- `cargo run -- --transpile source.wand` to transpile to JavaScript
- `cargo run` to run the REPL
- `./run_e2e_tests.sh` to run test suite
